{-# LANGUAGE FlexibleContexts, LambdaCase, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}

module G2.Verify.Interface ( VerifyResult (..)
                           , verifyFromFile) where

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Execution
import G2.Execution.InstTypes
import G2.Execution.HPC
import G2.Language
import qualified G2.Language.TypeClasses.TypeClasses as TC
import qualified G2.Language.CallGraph as G
import qualified G2.Language.KnownValues as KV
import G2.Lib.Printers
import qualified G2.Language.ExprEnv as E
import G2.Solver
import G2.Translation
import G2.Verify.Config
import G2.Verify.Reducer

import Control.Exception
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as S
import Data.IORef
import Data.Maybe
import System.Clock
import qualified G2.Language.TyVarEnv as TV

data VerifyResult = Verified
                  | Counterexample [ExecRes VerifierTracker]
                  | VerifyTimeOut
                  deriving (Show, Read)

type VerStack m = SM.StateT (ApproxPrevs VerifierTracker)
                        (SM.StateT LengthNTrack
                            (SM.StateT PrettyGuide m))

verifyRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                    State VerifierTracker
                 -> solver
                 -> simplifier
                 -> Config
                 -> VerifyConfig
                 -> S.HashSet Name -- ^ Names of functions that should not result in a larger expression become EXEC,
                                   -- but should not be added to the NRPC at the top level.
                 -> IO ( SomeReducer (VerStack m) VerifierTracker
                       , SomeHalter (VerStack m) (ExecRes VerifierTracker) VerifierTracker
                       , SomeOrderer (VerStack m) (ExecRes VerifierTracker) VerifierTracker
                       , IORef TimedOut)
verifyRedHaltOrd s solver simplifier config verify_config no_nrpc_names = do
    time_logger <- acceptTimeLogger
    (time_halter, io_timed_out) <- stdTimerHalter (fromInteger . toInteger $ timeLimit config)

    let labelApproxPoints s
            | Data (DataCon { dc_name = d }) <- getExpr s
            , d == dc_name (mkDCFalse (known_values s) (type_env s)) =
                                    "state" ++ show (length $ rules s) ++ "_ap"
            | otherwise = "state" ++ show (length $ rules s)

    m_logger <- fmap SomeReducer <$> getLimLogger' labelApproxPoints config prettyVerifierTracker

    let share = sharing config

        approx_no_inline = S.fromList
                         . E.keys
                         . E.filterConcOrSym (\case E.Conc _ -> True; E.Sym _ -> False)
                         $ expr_env s
                         
        strict_red f = case strict config of
                            True -> SomeReducer (verifyHigherOrderHandling ~> stdRed share f solver simplifier ~> instTypeRed ~> strictRed)
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

        set_focus_red f = SomeReducer adjustFocusReducer .~> logger_std_red f

        syntactic_eq_red f = case syntactic_eq_ra verify_config of
                                True -> SomeReducer (unifyNRPCReducer no_nrpc_names) .~> set_focus_red f
                                False -> set_focus_red f

        nrpc_approx_red f = case rev_abs verify_config of
                                True -> let nrpc_approx = nrpcAnyCallReducer no_nrpc_names verify_config config in
                                            SomeReducer nrpc_approx
                                        .~> syntactic_eq_red f
                                False -> logger_std_red f
        
        halter = switchEveryNHalter 20
                 <~> acceptIfViolatedHalter
                 <~> time_halter
                 <~> discardOnFalse

        inconsistent_halter = case syntactic_eq_ra verify_config of
                                    True -> SomeHalter (inconsistentNRPCHalter no_nrpc_names <~> halter)
                                    False -> SomeHalter halter

        halter_approx_discard = case approx verify_config of
                                        True -> SomeHalter (approximationHalter solver approx_no_inline) .<~> inconsistent_halter
                                        False -> inconsistent_halter

        orderer = case search_strat config of
                        Subpath -> SomeOrderer . liftOrderer $ lengthNSubpathOrderer (subpath_length config)
                        Iterative -> SomeOrderer $ pickLeastUsedOrderer

    return ( nrpc_approx_red (\_ _ _ _ -> Nothing) .== Finished --> verifySolveNRPC
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
               -> VerifyConfig
               -> IO (VerifyResult, Double, Bindings, Id)
verifyFromFile proj src f transConfig config verify_config = do
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
                                    Nothing False f (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys config' TV.empty)
                                    transConfig config'
    let (init_state', ng) = wrapCurrExpr (name_gen bindings) init_state
        bindings' = bindings { name_gen = ng }
    
    SomeSolver solver <- initSolver config
    let m_eq_tc = map (idName . snd)
              <$> lookupTCDicts (KV.eqTC $ known_values init_state') (type_classes init_state')
        eq_tc = fromMaybe [] m_eq_tc
        (state', bindings'') = runG2Pre (addSearchNames eq_tc $ emptyMemConfig) init_state' bindings'

        simplifier = FloatSimplifier :>> ArithSimplifier :>> BoolSimplifier :>> StringSimplifier :>> EqualitySimplifier
        --exp_env_names = E.keys . E.filterConcOrSym (\case { E.Sym _ -> False; E.Conc _ -> True }) $ expr_env state
        callGraph = G.getCallGraph $ expr_env state'
        reachable_funcs = concatMap (flip G.reachable callGraph) $ idName entry_f:eq_tc

        non_rec_funcs = filter (G.isFuncNonRecursive callGraph) reachable_funcs
        dicts = map idName $ TC.tcDicts (type_classes state')
        no_nrpc_names = non_rec_funcs ++ dicts

    -- analysis1 <- if states_at_time config then do l <- logStatesAtTime; return [l] else return noAnalysis
    -- let analysis2 = if states_at_step config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift . SM.lift $ logStatesAtStep s p xs] else noAnalysis
    --     analysis3 = if print_num_red_rules config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift . SM.lift . SM.lift $ logRedRuleNum s p xs] else noAnalysis
    --     analysis = analysis1 ++ analysis2 ++ analysis3

    let verifier_state = state' { track = initVerifierTracker }

    init_time <- getTime Realtime
    rho <- verifyRedHaltOrd verifier_state solver simplifier config' verify_config (S.fromList no_nrpc_names)
    let to = case rho of (_, _, _, to_)-> to_
    (er, bindings''') <-
            case rho of
                (red, hal, ord, _) ->
                        SM.evalStateT
                                (SM.evalStateT
                                    (SM.evalStateT
                                        (runG2WithSomes' red hal ord [] solver simplifier verifier_state bindings'')
                                        emptyApproxPrevs
                                    )
                                    lnt
                                )
                                (if showType config == Lax 
                                then mkPrettyGuide ()
                                else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
    
    to' <- readIORef to
    accept_time <- getTime Realtime
    let diff = diffTimeSpec accept_time init_time
        diff_secs = (fromInteger (toNanoSecs diff)) / (10 ^ (9 :: Int) :: Double)
    let res = case to' of
                TimedOut -> VerifyTimeOut
                NoTimeOut | false_er <- filter (currExprIsFalse . final_state) er
                          , not (null false_er) -> Counterexample false_er
                          | otherwise -> assert (all (currExprIsTrue . final_state) er) Verified
    return (res, diff_secs, bindings''', entry_f)
