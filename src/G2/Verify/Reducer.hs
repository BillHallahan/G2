{-# LANGUAGE FlexibleContexts, MultiWayIf, OverloadedStrings #-}

module G2.Verify.Reducer ( NRPCMemo
                         , nrpcAnyCallReducer
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
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Sequence

type NRPCMemo = HM.HashMap Expr Id

-- | When a newly reached function application is approximated by a previously seen (and thus explored) function application,
-- shift the new function application into the NRPCs.
nrpcAnyCallReducer :: MonadIO m =>
                      HS.HashSet Name -- ^ Names of functions that should not be approximated
                   -> Config
                   -> Reducer m Int NRPCMemo
nrpcAnyCallReducer no_nrpc_names config =
    (mkSimpleReducer (const 0) red)
            { onAccept = \s b nrpc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

    where        
        red rv s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv, tyvar_env = tvnv }) b
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , let (e, stripped_stack) = applyWrap (getExpr s) (exec_stack s)
            , v@(Var (Id n _)):es@(_:_) <- unApp . stripNRBT $ e = do
                -- Given a function call `f x1 ... xn`, we move the entire call to `f` into an NRPC
                -- Note that createNewCond wraps the function call with a Tick.
                -- This prevents that same function call from being immediately turned back into an NRPC
                -- when it is removed from the NRPCs.
                -- (2)
                -- Replace the entire expression with an NRPC
                if
                    -- Line (*) make sure we don't add back to NRPCs immediately.
                    | not (hasNRBT e) -- (*)
                    , Var (Id n _):_:_ <- unApp e

                    , Just n' <- E.deepLookupVar n eenv
                    , not (n' `HS.member` no_nrpc_names)
                    , not (E.isSymbolic n' eenv)

                    , not . isTyFun . typeOf tvnv $ e -> do
                        liftIO . putStrLn $ "e = " ++ show e ++ "\ntrack s = " ++ show (track s)
                        -- Reuse a previous symbolic variable that stood in for the same expression, if possible:
                        case HM.lookup e (track s) of
                            Just sym -> do
                                let s' = s { curr_expr = CurrExpr Evaluate (Var sym), exec_stack = stripped_stack }
                                return (Finished, [(s', rv)], b)
                            -- Try to get a new non-reduced path constraint if there is not an existing symbolic variable
                            Nothing ->
                                case createNonRed (name_gen b) s of
                                    Just (nr_s, new_sym, added_e, ng') -> do
                                        let memo = HM.insert e new_sym $ track s
                                        return (Finished, [(nr_s { track = memo }, rv + 1)], b { name_gen = ng' })
                                    Nothing -> return (Finished, [(s, rv)], b)
                    | otherwise -> return (Finished, [(s, rv)], b)
                
            | Tick nl (Var (Id n _)) <- ce
            , isNonRedBlockerTick nl
            , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
        red rv s b = return (Finished, [(s, rv)], b)
        
        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap e stck | Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (App e a) stck'
                         | otherwise = (e, stck)
        
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
                                , non_red_path_conds = nrs :|> (nre1, nre2)
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