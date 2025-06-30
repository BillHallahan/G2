{-# LANGUAGE FlexibleContexts, LambdaCase, OverloadedStrings #-}

module G2.Verify.Interface ( VerifyResult (..)
                           , verifyFromFile) where

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Execution
import G2.Execution.InstTypes
import G2.Execution.HPC
import G2.Language
import qualified G2.Language.CallGraph as G
import G2.Lib.Printers
import qualified G2.Language.ExprEnv as E
import G2.Solver
import G2.Translation
import G2.Verify.Reducer

import Control.Exception
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as S
import Data.IORef

data VerifyResult = Verified
                  | Counterexample [ExecRes ()]
                  | VerifyTimeOut
                  deriving (Show, Read)

type VerStack m = SM.StateT (ApproxPrevs ())
                        (SM.StateT LengthNTrack
                            (SM.StateT PrettyGuide m))

verifyRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                    State ()
                 -> solver
                 -> simplifier
                 -> Config
                 -> S.HashSet Name -- ^ Names of functions that should not result in a larger expression become EXEC,
                                   -- but should not be added to the NRPC at the top level.
                 -> IO ( SomeReducer (VerStack m) ()
                       , SomeHalter (VerStack m) (ExecRes ()) ()
                       , SomeOrderer (VerStack m) (ExecRes ()) ()
                       , IORef TimedOut)
verifyRedHaltOrd s solver simplifier config no_nrpc_names = do
    time_logger <- acceptTimeLogger
    (time_halter, io_timed_out) <- stdTimerHalter (fromInteger . toInteger $ timeLimit config)

    m_logger <- fmap SomeReducer <$> getLimLogger config

    let share = sharing config

        approx_no_inline = S.fromList
                         . E.keys
                         . E.filterConcOrSym (\case E.Conc _ -> True; E.Sym _ -> False)
                         $ expr_env s
                         
        strict_red f = case strict config of
                            True -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed ~> strictRed)
                            False -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed)

        nrpc_higher_red f = liftSomeReducer (strict_red f)
        
        accept_time_red f = case accept_times config of
                                True -> SomeReducer time_logger .~> nrpc_higher_red f
                                False -> nrpc_higher_red f

        num_steps_red f = case print_num_red_rules_per_state config of
                                True -> SomeReducer numStepsLogger .~> accept_time_red f
                                False -> accept_time_red f

        logger_std_red f = case m_logger of
                            Just logger -> liftSomeReducer $ liftSomeReducer (logger .~> num_steps_red f)
                            Nothing -> liftSomeReducer $ liftSomeReducer (num_steps_red f)

        nrpc_approx_red f = let nrpc_approx = nrpcApproxReducer solver approx_no_inline no_nrpc_names config in
                                        SomeReducer nrpc_approx .== Finished .--> logger_std_red f

        halter = switchEveryNHalter 20
                 <~> acceptIfViolatedHalter
                 <~> time_halter

        halter_approx_discard = SomeHalter (approximationHalter solver approx_no_inline <~> halter)

        orderer = case search_strat config of
                        Subpath -> SomeOrderer . liftOrderer $ lengthNSubpathOrderer (subpath_length config)
                        Iterative -> SomeOrderer $ pickLeastUsedOrderer

    return $
        case higherOrderSolver config of
            AllFuncs ->
                ( nrpc_approx_red retReplaceSymbFuncVar .== Finished .--> SomeReducer verifierSolverNRPC
                , halter_approx_discard
                , orderer
                , io_timed_out)
            SingleFunc ->
                ( nrpc_approx_red retReplaceSymbFuncVar .== Finished --> verifierSolverNRPC
                , halter_approx_discard
                , orderer
                , io_timed_out)
            SymbolicFunc ->
                ( nrpc_approx_red retReplaceSymbFuncTemplate .== Finished --> verifierSolverNRPC
                , halter_approx_discard
                , orderer
                , io_timed_out)

wrapCurrExpr :: NameGen -> State t -> (State t, NameGen)
wrapCurrExpr ng s@(State { curr_expr = CurrExpr er e, type_env = tenv, known_values = kv }) =
  let
    t = tyBool kv
    (binder, ng') = freshName ng
    
    true_dc = mkDCTrue kv tenv 
    false_dc = mkDCFalse kv tenv
    true_e = mkTrue kv
    false_e = mkFalse kv
    -- Introducing a case split (1) allows us to discard branches that just lead to true, without bothering
    -- to solve NRPCs and (2) ensures that we will search for a path that leads to false when solving NRPCs
    e' = Case e (Id binder t) t [ Alt (DataAlt true_dc []) (Assume Nothing false_e true_e)
                                , Alt (DataAlt false_dc []) false_e]
  in
  (s { curr_expr = CurrExpr er e' }, ng')

verifyFromFile :: [FilePath]
               -> [FilePath]
               -> StartFunc
               -> TranslationConfig
               -> Config
               -> IO (VerifyResult, Bindings, Id)
verifyFromFile proj src f transConfig config = do
    let config' = config {
                         -- For soundness, we must exhaustively search all states that are not discarded via approximation,
                         -- so we disable the step count.
                           step_limit = False
                         -- For soundness, cannot limit number of outputs explored 
                         , maxOutputs = Nothing
                         -- Not using hpc ticks
                         , hpc_discard_strat = False
                         -- Use approximation to add repeated function calls to NRPCs
                         , approx_nrpc = Nrpc
                         -- Use approximation to discard states that are approximated by previously explored states
                         , approx_discard = True
                         , higherOrderSolver = AllFuncs }


    (init_state, entry_f, bindings, _) <- initialStateFromFile proj src
                                    Nothing False f (mkCurrExpr Nothing Nothing) mkArgTys
                                    transConfig config'
    let (init_state', ng) = wrapCurrExpr (name_gen bindings) init_state
        bindings' = bindings { name_gen = ng }

    
    SomeSolver solver <- initSolver config
    let (state', bindings'') = runG2Pre emptyMemConfig init_state' bindings'

        simplifier = FloatSimplifier :>> ArithSimplifier :>> BoolSimplifier :>> StringSimplifier :>> EqualitySimplifier
        --exp_env_names = E.keys . E.filterConcOrSym (\case { E.Sym _ -> False; E.Conc _ -> True }) $ expr_env state
        callGraph = G.getCallGraph $ expr_env state'
        reachable_funcs = G.reachable (idName entry_f) callGraph

        non_rec_funcs = filter (G.isFuncNonRecursive callGraph) reachable_funcs

    -- analysis1 <- if states_at_time config then do l <- logStatesAtTime; return [l] else return noAnalysis
    -- let analysis2 = if states_at_step config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift . SM.lift $ logStatesAtStep s p xs] else noAnalysis
    --     analysis3 = if print_num_red_rules config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift . SM.lift . SM.lift $ logRedRuleNum s p xs] else noAnalysis
    --     analysis = analysis1 ++ analysis2 ++ analysis3

    rho <- verifyRedHaltOrd state' solver simplifier config' (S.fromList non_rec_funcs)
    let to = case rho of (_, _, _, to_)-> to_
    (er, bindings''') <-
            case rho of
                (red, hal, ord, _) ->
                        SM.evalStateT
                                (SM.evalStateT
                                    (SM.evalStateT
                                        (runG2WithSomes' red hal ord [] solver simplifier state' bindings'')
                                        emptyApproxPrevs
                                    )
                                    lnt
                                )
                                (if showType config == Lax 
                                then mkPrettyGuide ()
                                else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
    
    to' <- readIORef to
    let res = case to' of
                TimedOut -> VerifyTimeOut
                NoTimeOut | false_er <- filter (isFalse . final_state) er
                          , not (null false_er) -> Counterexample false_er
                          | otherwise -> assert (all (isTrue . final_state) er) Verified
    return (res, bindings''', entry_f)
    where
        isFalse s | E.deepLookupExpr (getExpr s) (expr_env s) == Just (mkFalse (known_values s ) ) = True
                  | otherwise = False

        isTrue s | E.deepLookupExpr (getExpr s) (expr_env s) == Just (mkTrue (known_values s)) = True
                 | otherwise = False