{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             MultiWayIf, OverloadedStrings, TupleSections, UndecidableInstances #-}

module G2.Verify.Reducer ( VerifierData
                         , initVerifierData
                         
                         , nrpcAnyCallReducer
                         , verifySolveNRPC
                         , verifyHigherOrderHandling
                         , lemmaGen
                         , approximationHalter
                         , lemmaHalter

                        , isLemmaState
                         
                         , discardOnFalse
                         , currExprIsFalse
                         , currExprIsTrue ) where

import G2.Config
import G2.Execution.Reducer
import G2.Interface
import G2.Language
import G2.Language.Approximation
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.NonRedPathConds
import qualified G2.Language.Stack as Stck
import qualified G2.Language.Typing as T
import G2.Solver

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import Data.List as L
import qualified Data.Map as M
import Data.Maybe
import G2.Language.ExprEnv (lookupConcOrSym)

data VerifierData t = VS { approx_states :: [State t] -- ^ States to check for approximation
                         , generated_lemmas :: [State t] -- ^ States generated as potential lemmas
                         }

instance ApproxHalterLog (VerifierData t) t where
    getApproxHalt = approx_states
    putApproxHalt s a = a { approx_states = s:(approx_states a) }

initVerifierData :: VerifierData t
initVerifierData = VS { approx_states = []
                      , generated_lemmas = [] }

-- | When a newly reached function application is approximated by a previously seen (and thus explored) function application,
-- shift the new function application into the NRPCs.
nrpcAnyCallReducer :: MonadIO m =>
                      HS.HashSet Name -- ^ Names of functions that should not be approximated
                   -> Config
                   -> Reducer m Int t
nrpcAnyCallReducer no_nrpc_names config =
    (mkSimpleReducer (const 0) red)
            { onAccept = \s b nrpc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

    where        
        red rv s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv, tyvar_env = tvnv }) b@(Bindings { name_gen = ng })
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , let wrapped_ce = applyWrap (getExpr s) (exec_stack s)
            , v@(Var (Id n _)):es@(_:_) <- unApp . stripNRBT $ wrapped_ce = do
                -- Given a function call `f x1 ... xn`, we move the entire call to `f` into an NRPC.
                -- Note that createNewCond wraps the function call with a Tick.
                -- This prevents that same function call from being immediately turned back into an NRPC
                -- when it is removed from the NRPCs.
                let e = applyWrap (getExpr s) (exec_stack s)
                    nr_s_ng = if
                                -- Line (*) make sure we don't add back to NRPCs immediately.
                                | not (hasNRBT wrapped_ce) -- (*)
                                , Var (Id n _):_:_ <- unApp e

                                , Just n' <- E.deepLookupVar n eenv
                                , not (n' `HS.member` no_nrpc_names)
                                , not (E.isSymbolic n' eenv)

                                , not . isTyFun . typeOf tvnv $ e -> createNonRed ng s
                                | otherwise -> Nothing
                
                case nr_s_ng of
                    Just (nr_s, _, _, ng') -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng' })
                    _ -> return (Finished, [(s, rv)], b)
            | Tick nl (Var (Id n _)) <- ce
            , isNonRedBlockerTick nl
            , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
        red rv s b = return (Finished, [(s, rv)], b)
        
        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap e stck | Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (App e a) stck'
                         | otherwise = e
        
        stripNRBT (Tick nl e) | isNonRedBlockerTick nl = e
        stripNRBT (App e1 e2) = App (stripNRBT e1) e2
        stripNRBT e = e

        hasNRBT (Tick nl e) | isNonRedBlockerTick nl = True
                            | otherwise = hasNRBT e
        hasNRBT (App e1 _) = hasNRBT e1
        hasNRBT _ = False

verifySolveNRPC :: Monad m => Reducer m () t
verifySolveNRPC = mkSimpleReducer (const ()) red
    where
        red _
                        s@(State {curr_expr = cexpr
                                , exec_stack = stck
                                , non_red_path_conds = nrs :<* (nre1, nre2)
                                })
                                b@(Bindings { name_gen = ng }) =
            
            let
                stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck
                s' = s { curr_expr = CurrExpr Evaluate nre1
                    , exec_stack = stck'
                    , non_red_path_conds = nrs }

                in return (InProgress, [(s', ())], b { name_gen = ng })
        red _ s b = return (Finished, [(s, ())], b)

verifyHigherOrderHandling :: MonadIO m => Reducer m () t
verifyHigherOrderHandling = mkSimpleReducer (const ()) red
    where
        red _ s@(State { curr_expr = CurrExpr _ ce
                       , expr_env = eenv
                       , type_env = tenv
                       , known_values = kv
                       , type_classes = tc 
                       , tyvar_env = tvnv }) b@(Bindings { name_gen = ng })
            | (App (Var (Id n ty_fun)) ar) <- ce
            , E.isSymbolic n eenv =
                let
                    ty_ar = typeOf tvnv ar
                    (lam_x, ng2) = freshId ty_ar ng
                    (bindee, ng3) = freshId ty_ar ng2

                    (ret_true, ng4) = freshId (returnType ty_fun) ng3
                    (ret_false, ng5) = freshId ty_fun ng4

                    eq_tc = case lookupTCDict tc (eqTC kv) ty_ar of
                                Just tc -> tc
                                Nothing -> error "verifyHigherOrderHandling: unsuported type"
                    eq_f = eqFunc kv
                    eq_f_i = Id eq_f (typeOf tvnv . fromJust $ E.lookup eq_f eenv)

                    e = mkApp [Var eq_f_i, Type ty_ar, Var eq_tc, Var lam_x, ar]

                    func_body =
                        Lam TermL lam_x $ 
                            Case e bindee (returnType ty_fun)
                                [ Alt (DataAlt (mkDCTrue kv tenv) []) (Var ret_true)
                                , Alt (DataAlt (mkDCFalse kv tenv) []) (App (Var ret_false) (Var lam_x))]

                    eenv' = E.insertSymbolic ret_true
                          . E.insertSymbolic ret_false
                          $ E.insert n func_body eenv

                    s' = s { curr_expr = CurrExpr Evaluate (App func_body ar), expr_env = eenv'}
                in
                return (InProgress, [(s', ())], b {name_gen = ng5})
        red _ s b = return (Finished, [(s, ())], b)


-- | If a state S has a current expression, path constraints, and NRPC set that are approximated by some
-- other state S', discard S. Any counterexample discoverable from S is also discoverable from S'.
approximationHalter :: (Named t, Solver solver, SM.MonadState (VerifierData t) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r t
approximationHalter = approximationHalter' (\_ s approx -> tags s == tags approx)

-- | Discard all other states if we find a counterexample.
discardOnFalse :: Monad m => Halter m () (ExecRes t) t
discardOnFalse = (mkSimpleHalter (\_ -> ())
                                (\hv _ _ -> hv)
                                (\_ _ _ -> return Continue)
                                (\hv _ _ _ -> hv))
                    { discardOnStart = \_ pr s -> discard s pr }
    where
        discard (State { expr_env = eenv, known_values = kv }) (Processed { accepted = acc })
            = any (\(ExecRes { final_state = s }) -> currExprIsFalse s && not (isLemmaState s)) acc

currExprIsBool :: Bool -> State t -> Bool
currExprIsBool b s = E.deepLookupExpr (getExpr s) (expr_env s) == mkBool (known_values s) b

currExprIsFalse :: State t -> Bool
currExprIsFalse = currExprIsBool False

currExprIsTrue :: State t -> Bool
currExprIsTrue = currExprIsBool False

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

isLemmaState :: State t -> Bool
isLemmaState = not . HS.null . tags

lemmaTag :: Name
lemmaTag = Name "LEMMA" Nothing 0 Nothing

-- Responsible for generating new potential lemmas
lemmaGen :: (Solver solver, SM.MonadState (VerifierData t) m, Named t, MonadIO m) =>
            solver
         -> HS.HashSet Name -- ^ Variables that should not be inlined
         -> Reducer m () t
lemmaGen solver no_inline =
    mkSimpleReducer (const ()) red
    where
        red _ s@(State { expr_env = eenv
                       , curr_expr = CurrExpr _ e
                       , known_values = kv
                       , non_red_path_conds = nrpcs })
              b@(Bindings { name_gen = ng })
            -- Only try to generate lemmas when we have hit False as the current expression.
            -- Slightly arbitrary choice, but we get False pretty often, and it stops us having
            -- to run these checks every step.
            | e == mkFalse kv
            , Stck.null (exec_stack s) = do
                let cand_nrpc = filter (\(_, e2) -> not . isVar $ E.deepLookupExpr e2 eenv) $ toListNRPC nrpcs
                    (ng', xs) = mapAccumR (createLemma s) ng cand_nrpc
                
                gen_lemmas <- SM.gets generated_lemmas
                let lemmaIsNew s = allM (\gl -> not <$> lemmaEquiv solver no_inline gl s) gen_lemmas
                xs' <- filterM lemmaIsNew xs

                SM.modify (\a -> a { generated_lemmas = xs' ++ generated_lemmas a})    

                return (Finished, (s, ()):map (, ()) xs', b { name_gen = ng'})
            | otherwise = return (Finished, [(s, ())], b)
        
        isVar (Tick _ e) = isVar e
        isVar (Var _) = True
        isVar _ = False

lemmaEquiv :: (Solver solver, Named t, MonadIO m) =>
              solver
           -> HS.HashSet Name -- ^ Variables that should not be inlined
           -> State t
           -> State t
           -> m Bool
lemmaEquiv solver no_inline s1 s2 = do
    r1 <- liftIO $ mr s1 s2
    r2 <- liftIO $ mr s2 s1
    return $ r1 && r2
    where
        mr_cont = mrContIgnoreNRPCTicks (\_ _ _ _ _ -> ()) lookupConcOrSymState
        mr = moreRestrictiveIncludingPCAndNRPC solver mr_cont (\_ _ _ _ _ -> ()) lookupConcOrSymState no_inline

createLemma :: State t ->  NameGen -> NRPC -> (NameGen, State t)
createLemma s ng (e1, e2) =
    let
        (lemma_tag, ng') = freshSeededName lemmaTag ng

        (empty_nrpc, ng'') = emptyNRPC ng'
        (ng''', nrpc) = addFirstNRPC ng'' e1 e2 empty_nrpc

        s' = s { curr_expr = CurrExpr Return . mkFalse $ known_values s
               , exec_stack = Stck.empty
               , non_red_path_conds = nrpc
               , tags = HS.insert lemma_tag (tags s) }
    in
    (ng''', s')              

-- Kill all lemma state if no non-lemma states remain
lemmaHalter :: Monad m => Halter m () r t
lemmaHalter =
    (mkSimpleHalter
        (const ())
        (\_ _ _ -> ())
        (\_ _ _ ->  return Continue)
        (\_ _ _ _ -> ())) { filterAllStates = fil }
    where
        fil m =
            if all (isLemmaState . getExState) . concat .  M.elems $ m
                then M.empty
                else m