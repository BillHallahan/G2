{-# LANGUAGE FlexibleContexts #-}

module G2.Verify.Reducer ( nrpcAnyCallReducer
                         , verifySolveNRPC
                         , verifyHigherOrderHandling
                         , approximationHalter ) where

import G2.Config
import G2.Execution.Reducer
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
import Data.Maybe


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
        red rv s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv }) b
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , let e = applyWrap (getExpr s) (exec_stack s)
            , Var (Id n _):_:_ <- unApp e

            , Just (Id n' _) <- E.deepLookupVar n eenv
            , not (n' `HS.member` no_nrpc_names)
            , not (E.isSymbolic n' eenv)

            , not . isTyFun . typeOf $ e = do
                -- liftIO $ do
                --     putStrLn $ "curr_expr s = " ++ show (getExpr s)
                --     putStrLn $ "log_path s = " ++ show (log_path s)
                --     putStrLn $ "num_steps s = " ++ show (num_steps s)
                let nr_s_ng = createNonRedQueue (name_gen b) s

                case nr_s_ng of
                    Just (nr_s, _, ng') -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng' })
                    _ -> return (Finished, [(s, rv)], b)
            | Tick nl (Var (Id n _)) <- ce
            , isNonRedBlockerTick nl
            , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
        red rv s b = return (Finished, [(s, rv)], b)
        
        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap e stck | Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (App e a) stck'
                         | otherwise = e

verifySolveNRPC :: Monad m => Reducer m () t
verifySolveNRPC = mkSimpleReducer (const ()) red
    where
        red _
                        s@(State {curr_expr = cexpr
                                , exec_stack = stck
                                , non_red_path_conds = (nre1, nre2) :*> nrs
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
        red _ s@(State { curr_expr = CurrExpr _ (App (Var (Id n ty_fun)) ar)
                       , expr_env = eenv
                       , type_env = tenv
                       , known_values = kv
                       , type_classes = tc }) b@(Bindings { name_gen = ng })
            | E.isSymbolic n eenv =
                let
                    ty_ar = typeOf ar
                    (lam_x, ng2) = freshId ty_ar ng
                    (bindee, ng3) = freshId ty_ar ng2

                    (ret_true, ng4) = freshId (returnType $ PresType ty_fun) ng3
                    (ret_false, ng5) = freshId ty_fun ng4

                    eq_tc = case lookupTCDict tc (eqTC kv) ty_ar of
                                Just tc -> tc
                                Nothing -> error "verifyHigherOrderHandling: unsuported type"
                    eq_f = eqFunc kv
                    eq_f_i = Id eq_f (typeOf . fromJust $ E.lookup eq_f eenv)

                    e = mkApp [Var eq_f_i, Type ty_ar, Var eq_tc, Var lam_x, ar]

                    func_body =
                        Lam TermL lam_x $ 
                            Case e bindee (returnType $ PresType ty_fun)
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
approximationHalter :: (Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r t
approximationHalter = approximationHalter' (\_ _ -> True)

