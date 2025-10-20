{-# LANGUAGE FlexibleContexts, MultiWayIf, OverloadedStrings #-}

module G2.Verify.Reducer ( nrpcAnyCallReducer
                         , adjustFocusReducer
                         , verifySolveNRPC
                         , verifyHigherOrderHandling
                         , approximationHalter
                         
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
import qualified G2.Language.Stack as Stck
import qualified G2.Language.Typing as T
import G2.Solver

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Sequence

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
                -- Replace each argument which is itself a function call with a NRPC.
                -- For instance:
                --  @ f (g x) y (h z)@
                -- Will get rewritten to:
                --  @ f s1 y s2 @
                -- with new NRPCs:
                --  @ s1 = g x 
                --    s2 = h z @
                let ((s', ng'), es') =
                        mapAccumR
                            (\(s_, ng_) e -> if
                                | buried_e <- E.deepLookupExpr e eenv 
                                , Var (Id ne _):_:_ <- unApp buried_e

                                , Just n' <- E.deepLookupVar ne eenv
                                , not (n' `HS.member` no_nrpc_names)
                                , not (E.isSymbolic n' eenv)

                                , not . isTyFun . typeOf tvnv $ buried_e
                                , Just (s_', sym_i, _, ng_') <- createNonRed' ng_ Unfocused s_ buried_e ->
                                    ((s_', ng_'), Var sym_i)
                                | otherwise -> ((s_, ng_), e)) (s, name_gen b) es
                let s'' = s' { curr_expr = CurrExpr Evaluate . mkApp $ v:es' }

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

                                , not . isTyFun . typeOf tvnv $ e -> createNonRed ng' (focused s'') s''
                                | otherwise -> Nothing
                
                case nr_s_ng of
                    Just (nr_s, _, _, ng'') -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng'' })
                    _ -> return (Finished, [(s'', rv)], b)
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

-- | Handles NRPC focuses:
--   (1) If we evaluate a variable when in a Focused state, set all NRPCs assigning to that variable to Focused
--   (2) If we have only unfocused NRPCs, empty the NRPCs
adjustFocusReducer :: Monad m => Reducer m () t
adjustFocusReducer = mkSimpleReducer (const ()) red
    where
        red rv s@(State { expr_env = eenv
                        , curr_expr = CurrExpr _ (Var (Id n _))
                        , non_red_path_conds = nrpc
                        , focused = Focused }) b =
            let
                s' = s { non_red_path_conds = setFocus n Focused eenv nrpc }
            in
            return (Finished, [(s', rv)], b)
        red rv s@(State {  non_red_path_conds = nrpc }) b@(Bindings { name_gen = ng } )
            | currExprIsFalse s, allNRPC (\(focus, _, _) -> focus == Unfocused) nrpc =
                let (empty_nrpc, ng') = emptyNRPC ng in
                return (Finished, [(s { non_red_path_conds = empty_nrpc }, rv)], b { name_gen = ng' } )
        red rv s b =
            return (Finished, [(s, rv)], b)


verifySolveNRPC :: Monad m => Reducer m () t
verifySolveNRPC = mkSimpleReducer (const ()) red
    where
        red _
                        s@(State {curr_expr = cexpr
                                , exec_stack = stck
                                , non_red_path_conds = nrs :<* (focus, nre1, nre2)
                                })
                                b@(Bindings { name_gen = ng }) =
            
            let
                stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck
                s' = s { curr_expr = CurrExpr Evaluate nre1
                       , exec_stack = stck'
                       , non_red_path_conds = nrs
                       , focused = focus }

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
approximationHalter :: (Named t, Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r t
approximationHalter = approximationHalter' (\_ _ -> True)

-- | Discard all other states if we find a counterexample.
discardOnFalse :: Monad m => Halter m () (ExecRes t) t
discardOnFalse = (mkSimpleHalter (\_ -> ())
                                (\hv _ _ -> hv)
                                (\_ _ _ -> return Continue)
                                (\hv _ _ _ -> hv))
                    { discardOnStart = \_ pr s -> discard s pr }
    where
        discard (State { expr_env = eenv, known_values = kv }) (Processed { accepted = acc })
            = any (currExprIsFalse . final_state) acc

currExprIsBool :: Bool -> State t -> Bool
currExprIsBool b s = E.deepLookupExpr (getExpr s) (expr_env s) == mkBool (known_values s) b

currExprIsFalse :: State t -> Bool
currExprIsFalse = currExprIsBool False

currExprIsTrue :: State t -> Bool
currExprIsTrue = currExprIsBool False