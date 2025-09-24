{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE BangPatterns, FlexibleContexts, LambdaCase, OverloadedStrings #-}

module G2.Interface.Interface ( MkCurrExpr
                              , CurrExprRes (..)
                              , MkArgTypes
                              , IT.SimpleState
                              , TimedOut (..)
                              , doTimeout
                              , maybeDoTimeout

                              , initStateWithCall
                              , initStateWithCall'
                              , initStateFromSimpleState
                              , initStateFromSimpleState'
                              , initStateFromSimpleStateWithCall
                              , initSimpleState

                              , mkArgTys
                              , noStartFuncMkCurrExpr
                              
                              , initRedHaltOrd
                              , initSolver
                              , initSolverInfinite
                              
                              , initialStateFromFileSimple
                              , initialStateFromFile
                              , initialStateNoStartFunc

                              , runG2FromFile
                              , runG2WithConfig
                              , runG2WithSomes
                              , runG2WithSomes'
                              , runG2Pre
                              , runG2Post
                              , runExecution
                              , runG2SolvingResult
                              , runG2Solving
                              , runG2
                              , Config) where

import GHC hiding (Name, entry, nameModule, Id, Type)
import GHC.Paths
import GHC.Driver.Monad
import GHC.Utils.Exception

import G2.Config.Config

import G2.Language

import G2.Initialization.Interface
import G2.Initialization.KnownValues
import G2.Execution.InstTypes
import G2.Initialization.MkCurrExpr
import qualified G2.Initialization.Types as IT
import G2.Preprocessing.Interface

import G2.Execution.HPC
import G2.Execution.Interface
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Execution.PrimitiveEval
import G2.Execution.Memory

import G2.Interface.ExecRes

import G2.Lib.Printers

import G2.Translation
import G2.Translation.ValidateState

import G2.Solver

import G2.Postprocessing.Interface

import qualified G2.Language.CallGraph as G
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack

import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.IORef
import Data.Maybe
import Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.List as L
import qualified G2.Language.TyVarEnv as TV
import System.Timeout

type AssumeFunc = T.Text
type AssertFunc = T.Text
type ReachFunc = T.Text

type MkCurrExpr = TypeClasses -> NameGen -> ExprEnv -> TypeEnv
                     -> KnownValues -> Config -> CurrExprRes

doTimeout :: Int -> IO a -> IO (Maybe a)
doTimeout secs action = do
  res <- timeout (secs * 1000 * 1000) action -- timeout takes micros.
  case res of
    Just _ -> return res
    Nothing -> do
      putStrLn "Timeout!"
      return Nothing

maybeDoTimeout :: Maybe Int -> IO a -> IO (Maybe a)
maybeDoTimeout (Just secs) = doTimeout secs
maybeDoTimeout Nothing = fmap Just


{-# INLINE initStateWithCall #-}
initStateWithCall :: ExtractedG2
                  -> Bool
                  -> StartFunc
                  -> [Maybe T.Text]
                  -> (Id -> MkCurrExpr)
                  -> (Expr -> MkArgTypes)
                  -> Config
                  -> (Id, State (), Bindings)
initStateWithCall exg2 useAssert f m_mod mkCurr argTys config =
    let
        s = initSimpleState exg2

        (ie, fe) = case findFunc TV.empty f m_mod (IT.expr_env s) of
                        Left ie' -> ie'
                        Right errs -> error errs
        
        (s', b) = initStateFromSimpleState s m_mod useAssert (mkCurr ie) (argTys fe) config
    in
    (ie, s', b)

{-# INLINE initStateWithCall' #-}
initStateWithCall' :: ExtractedG2
                   -> StartFunc
                   -> [Maybe T.Text]
                   -> (Id -> MkCurrExpr)
                   -> (Expr -> MkArgTypes)
                   -> Config
                   -> (Id, State (), Bindings)
initStateWithCall' exg2 =
    initStateWithCall exg2 False

{-# INLINE initStateFromSimpleStateWithCall #-}
initStateFromSimpleStateWithCall :: IT.SimpleState
                                 -> Bool
                                 -> StartFunc
                                 -> [Maybe T.Text]
                                 -> (Id -> MkCurrExpr)
                                 -> (Expr -> MkArgTypes)
                                 -> Config
                                 -> (State (), Id, Bindings)
initStateFromSimpleStateWithCall simp_s useAssert f m_mod mkCurr argTys config =
    let
        (ie, fe) = case findFunc TV.empty f m_mod (IT.expr_env simp_s) of
                        Left ie' -> ie'
                        Right errs -> error errs
    
        (s, b) = initStateFromSimpleState simp_s m_mod useAssert (mkCurr ie) (argTys fe) config
    in
    (s, ie, b)

initStateFromSimpleState :: IT.SimpleState
                         -> [Maybe T.Text]
                         -> Bool
                         -> MkCurrExpr
                         -> MkArgTypes
                         -> Config
                         -> (State (), Bindings)
initStateFromSimpleState s m_mod useAssert mkCurr argTys config =
    let
        s' = runInitialization2 config s argTys
        eenv' = IT.expr_env s'
        tenv' = IT.type_env s'
        ng' = IT.name_gen s'
        hs = IT.handles s'
        kv' = IT.known_values s'
        tc' = IT.type_classes s'
        fams = IT.families s'
        CurrExprRes { ce_expr = ce
                    , fixed_in = f_i
                    , symbolic_type_ids = typ_is
                    , symbolic_value_ids = val_is
                    , in_coercion = m_coercion
                    , mkce_namegen = ng'' } = mkCurr tc' ng' eenv' tenv' kv' config
    in
    (State {
      expr_env = foldr E.insertSymbolic eenv' val_is
    , type_env = tenv'
    , tyvar_env = foldr TV.insertSymbolic TV.empty typ_is
    , curr_expr = CurrExpr Evaluate ce
    , path_conds = PC.fromList []
    , non_red_path_conds = emptyNRPC
    , handles = hs
    , mutvar_env = HM.empty
    , true_assert = if useAssert || check_asserts config then False else True
    , assert_ids = Nothing
    , type_classes = tc'
    , families = fams
    , exec_stack = Stack.empty
    , model = HM.empty
    , known_values = kv'
    , rules = []
    , num_steps = 0
    , track = ()
    , sym_gens = Seq.empty
    , reached_hpc = S.empty
    , tags = S.empty

    , log_path = []
    }
    , Bindings {
      fixed_inputs = f_i
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = map idName $ typ_is ++ val_is
    , input_coercion = m_coercion
    , higher_order_inst = S.filter (\n -> nameModule n `elem` m_mod) . S.fromList $ IT.exports s
    , rewrite_rules = IT.rewrite_rules s
    , name_gen = ng''
    , exported_funcs = IT.exports s })

mkArgTys :: TV.TyVarEnv -> Expr -> MkArgTypes
mkArgTys tv e simp_s =
    snd $ instantiateArgTypes tv (IT.type_classes simp_s) (IT.known_values simp_s) e

{-# INLINE initStateFromSimpleState' #-}
initStateFromSimpleState' :: IT.SimpleState
                          -> StartFunc
                          -> [Maybe T.Text]
                          -> Config
                          -> (State (), Bindings)
initStateFromSimpleState' s sf m_mod =
    let
        (ie, fe) = case findFunc TV.empty sf m_mod (IT.expr_env s) of
                          Left ie' -> ie'
                          Right errs -> error errs
    in
    initStateFromSimpleState s m_mod False (mkCurrExpr TV.empty Nothing Nothing ie) (mkArgTys TV.empty fe)

{-# INLINE initSimpleState #-}
initSimpleState :: ExtractedG2
                -> IT.SimpleState
initSimpleState (ExtractedG2 { exg2_binds = prog
                             , exg2_tycons = prog_typ
                             , exg2_classes = cls
                             , exg2_axioms = axs
                             , exg2_exports = es
                             , exg2_rules = rs }) =
    let
        eenv = E.fromExprMap prog
        tenv = mkTypeEnv prog_typ
        tc = initTypeClasses TV.empty cls
        fams = mkFamilies axs
        kv = initKnownValues eenv tenv tc
        ng = mkNameGen (prog, prog_typ, rs)

        s = IT.SimpleState { IT.expr_env = eenv
                           , IT.type_env = tenv
                           , IT.name_gen = ng
                           , IT.handles = HM.empty
                           , IT.known_values = kv
                           , IT.type_classes = tc
                           , IT.families = fams
                           , IT.rewrite_rules = rs
                           , IT.exports = es }
    in
    runInitialization1 s

initCheckReaches :: State t -> Maybe T.Text -> Maybe ReachFunc -> State t
initCheckReaches s@(State { expr_env = eenv
                          , known_values = kv 
                          , tyvar_env = tvnv}) m_mod reaches =
    s {expr_env = checkReaches tvnv eenv kv reaches m_mod }

type RHOStack m t = SM.StateT (ApproxPrevs t)
                        (SM.StateT LengthNTrack
                            (SM.StateT PrettyGuide
                                (SM.StateT HpcTracker
                                    (SM.StateT HPCMemoTable m))))

{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer (RHOStack IO ()) rv ()
                          -> Halter (RHOStack IO ()) hv (ExecRes ()) ()
                          -> Orderer (RHOStack IO ()) sov b (ExecRes ()) ()
                          -> (State () -> Bindings -> RHOStack IO () (Maybe (ExecRes ())))
                          -> [AnalyzeStates (RHOStack IO ()) (ExecRes ()) ()]
                          -> State ()
                          -> Bindings
                          -> (RHOStack IO ()) (Processed (ExecRes ()) (State ()), Bindings)
    #-}

{-# SPECIALIZE 
    initRedHaltOrd :: (Solver solver, Simplifier simplifier) =>
                      State ()
                   -> S.HashSet (Maybe T.Text)
                   -> solver
                   -> simplifier
                   -> Config
                   -> S.HashSet Name
                   -> S.HashSet Name
                   -> IO ( SomeReducer (RHOStack IO ()) ()
                         , SomeHalter (RHOStack IO ()) (ExecRes ()) ()
                         , SomeOrderer (RHOStack IO ()) (ExecRes ()) ()
                         , IORef TimedOut)
    #-}
initRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                  State ()
               -> S.HashSet (Maybe T.Text)
               -> solver
               -> simplifier
               -> Config
               -> S.HashSet Name -- ^ Names of functions that may not be added to NRPCs
               -> S.HashSet Name -- ^ Names of functions that should not reesult in a larger expression become EXEC,
                                 -- but should not be added to the NRPC at the top level.
               -> IO ( SomeReducer (RHOStack m ()) ()
                     , SomeHalter (RHOStack m ()) (ExecRes ()) ()
                     , SomeOrderer (RHOStack m ()) (ExecRes ()) ()
                     , IORef TimedOut)
initRedHaltOrd s mod_name solver simplifier config exec_func_names no_nrpc_names = do
    time_logger <- acceptTimeLogger
    (time_halter, io_timed_out) <- stdTimerHalter (fromInteger . toInteger $ timeLimit config)

    m_logger <- fmap SomeReducer <$> getLimLogger config

    on_acc_hpc_red <- onAcceptHpcReducer s mod_name

    let share = sharing config

        state_name = Name "state" Nothing 0 Nothing

        approx_no_inline = S.fromList
                         . E.keys
                         . E.filterConcOrSym (\case E.Conc _ -> True; E.Sym _ -> False)
                         $ expr_env s
                         
        strict_red f = case strict config of
                            True -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed ~> strictRed)
                            False -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed)

        hpc_red f = case hpc config of
                        -- True ->  SomeReducer (immedHpcReducer mod_name) .~> strict_red f 
                        True ->  SomeReducer on_acc_hpc_red .~> strict_red f 
                        False -> strict_red f

        nrpc_lib_red f = case lib_nrpc config of
                                Nrpc -> liftSomeReducer
                                            (SomeReducer (nonRedLibFuncsReducer
                                                                        exec_func_names
                                                                        no_nrpc_names
                                                                        config
                                                        ) .== Finished .--> hpc_red f)
                                NoNrpc -> liftSomeReducer (hpc_red f)

        nrpc_higher_red f = case symbolic_func_nrpc config of
                                Nrpc -> SomeReducer (nonRedHigherOrderReducer config) .== Finished .--> nrpc_lib_red f
                                NoNrpc -> nrpc_lib_red f
        
        accept_time_red f = case accept_times config of
                                True -> SomeReducer time_logger .~> nrpc_higher_red f
                                False -> nrpc_higher_red f

        num_steps_red f = case print_num_red_rules_per_state config of
                                True -> SomeReducer numStepsLogger .~> accept_time_red f
                                False -> accept_time_red f

        logger_std_red f = case m_logger of
                            Just logger -> liftSomeReducer $ liftSomeReducer (logger .~> num_steps_red f)
                            Nothing -> liftSomeReducer $ liftSomeReducer (num_steps_red f)

        nrpc_approx_red f = case approx_nrpc config of
                                Nrpc -> let nrpc_approx = nrpcApproxReducer solver approx_no_inline no_nrpc_names config in
                                        SomeReducer nrpc_approx .== Finished .--> logger_std_red f
                                NoNrpc -> logger_std_red f

        halter = switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config)
                 <~> acceptIfViolatedHalter
                 <~> time_halter

        halter_step = case step_limit config of
                            True -> SomeHalter (zeroHalter (steps config) <~> halter)
                            False -> SomeHalter halter
        
        -- halter_accept_only = case halter_step of SomeHalter h -> SomeHalter (liftHalter (liftHalter (liftHalter (acceptOnlyNewHPC h))))

        halter_hpc_discard = case hpc_discard_strat config of
                                    True -> SomeHalter (liftHalter . liftHalter . liftHalter . liftHalter $ noNewHPCHalter mod_name) .<~> halter_step
                                    False -> halter_step

        halter_approx_discard = case approx_discard config of
                                    True ->
                                        SomeHalter (hpcApproximationHalter solver approx_no_inline) .<~> halter_hpc_discard
                                    False -> halter_hpc_discard

        orderer = case search_strat config of
                        Subpath -> SomeOrderer . liftOrderer $ lengthNSubpathOrderer (subpath_length config)
                        Iterative -> SomeOrderer $ pickLeastUsedOrderer

    return $
        case higherOrderSolver config of
            AllFuncs ->
                ( nrpc_approx_red retReplaceSymbFuncVar .== Finished .--> SomeReducer nonRedPCRed
                , SomeHalter (discardIfAcceptedTagHalter True state_name) .<~> halter_approx_discard
                , orderer
                , io_timed_out)
            SingleFunc ->
                ( nrpc_approx_red retReplaceSymbFuncVar .== Finished .--> taggerRed state_name :== Finished --> nonRedPCRed
                , SomeHalter (discardIfAcceptedTagHalter True state_name) .<~> halter_approx_discard
                , orderer
                , io_timed_out)
            SymbolicFunc ->
                ( nrpc_approx_red retReplaceSymbFuncTemplate .== Finished .--> taggerRed state_name :== Finished --> nonRedPCSymFuncRed
                , SomeHalter (discardIfAcceptedTagHalter True state_name) .<~> halter_approx_discard
                , orderer
                , io_timed_out)

initSolver :: Config -> IO SomeSolver
initSolver = initSolver' arbValue

initSolverInfinite :: Config -> IO SomeSolver
initSolverInfinite = initSolver' arbValueInfinite

initSolver' :: ArbValueFunc -> Config -> IO SomeSolver
initSolver' avf config = do
    SomeSMTSolver con <- getSMTAV avf config
    let adt_num = ADTNumericalSolver avf con
    some_adt_solver <- case print_num_solver_calls config of
            True -> return . SomeSolver =<< callsSolver "SMT" adt_num
            False -> return $ SomeSolver adt_num
    some_adt_solver' <- case time_solving config of
            True -> timeSomeSolver "SMT" some_adt_solver
            False -> return some_adt_solver
    some_adt_solver'' <- case print_solver_sol_counts config of
                                True -> countResultsSomeSolver some_adt_solver'
                                False -> return some_adt_solver'

    let con' = case some_adt_solver'' of
                    SomeSolver adt_solver ->
                        SomeSolver -- . CommonSubExpElim
                                   $ GroupRelated avf
                                    ( UndefinedHigherOrder
                                 :?> EqualitySolver
                                 :?> adt_solver)

    con'' <- case time_solving config of
                True -> timeSomeSolver "General" con'
                False -> return con'

    case print_num_solver_calls config of
                True -> callsSomeSolver "General" con''
                False -> return con''

mkTypeEnv :: HM.HashMap Name AlgDataTy -> TypeEnv
mkTypeEnv = id

{-# INLINE initialStateFromFileSimple #-}
initialStateFromFileSimple :: [FilePath]
                   -> [FilePath]
                   -> StartFunc
                   -> (Id -> MkCurrExpr)
                   -> (Expr -> MkArgTypes)
                   -> Config
                   -> IO (State (), Id, Bindings, [Maybe T.Text])
initialStateFromFileSimple  proj src f mkCurr argTys config =
    initialStateFromFile proj src Nothing False f mkCurr argTys simplTranslationConfig config

initialStateNoStartFunc :: [FilePath]
                     -> [FilePath]
                     -> TranslationConfig
                     -> Config
                     -> IO (State (), Bindings)
initialStateNoStartFunc proj src transConfig config = do
    (_, exg2) <- translateLoaded proj src transConfig config

    let simp_state = initSimpleState exg2

        (init_s, bindings) = initStateFromSimpleState simp_state [Nothing] False
                                 noStartFuncMkCurrExpr
                                 (E.higherOrderExprs TV.empty . IT.expr_env)
                                 config

    return (init_s, bindings)

noStartFuncMkCurrExpr :: a -> NameGen -> b -> c -> d -> e -> CurrExprRes
noStartFuncMkCurrExpr _ ng _ _ _ _ =
    CurrExprRes
        { ce_expr = Prim Undefined TyBottom
        , fixed_in = []
        , symbolic_type_ids = []
        , symbolic_value_ids = []
        , in_coercion = Nothing
        , mkce_namegen = ng }

initialStateFromFile :: [FilePath]
                     -> [FilePath]
                     -> Maybe ReachFunc
                     -> Bool
                     -> StartFunc
                     -> (Id -> MkCurrExpr)
                     -> (Expr -> MkArgTypes)
                     -> TranslationConfig
                     -> Config
                     -> IO (State (), Id, Bindings, [Maybe T.Text])
initialStateFromFile proj src m_reach def_assert f mkCurr argTys transConfig config = do
    (mb_modname, exg2) <- translateLoaded proj src transConfig config

    let simp_state = initSimpleState exg2
        (ie, fe) = case findFunc TV.empty f mb_modname (IT.expr_env simp_state) of
                        Left ie' -> ie'
                        Right errs -> error errs

        spec_mod = nameModule . idName $ ie

        (init_s, bindings) = initStateFromSimpleState simp_state mb_modname def_assert
                                                  (mkCurr ie) (argTys fe) config
    
        reaches_state = initCheckReaches init_s spec_mod m_reach

    return (reaches_state, ie, bindings, mb_modname)

runG2FromFile :: [FilePath]
              -> [FilePath]
              -> [GeneralFlag]
              -> Maybe AssumeFunc
              -> Maybe AssertFunc
              -> Maybe ReachFunc
              -> Bool
              -> String
              -> TranslationConfig
              -> Config
              -> IO ([ExecRes ()], Bindings, TimedOut, Id)
runG2FromFile proj src gflags m_assume m_assert m_reach def_assert f transConfig config = do
    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile  proj src
                                    m_reach def_assert (T.pack f) (mkCurrExpr TV.empty m_assume m_assert) (mkArgTys TV.empty)
                                    transConfig config

    (er, b, to) <- runG2WithConfig proj src entry_f f gflags mb_modname init_state config bindings

    return (er, b, to, entry_f)

runG2WithConfig :: [FilePath]-> [FilePath] -> Id -> String -> [GeneralFlag] -> [Maybe T.Text] -> State () -> Config -> Bindings
                -> IO ( [ExecRes ()]
                      , Bindings
                      , TimedOut -- ^ Did any states timeout?
                      )
runG2WithConfig proj src entry_f f gflags mb_modname state@(State { expr_env = eenv}) config bindings = do
    SomeSolver solver <- initSolver config
    let (state', bindings') = runG2Pre emptyMemConfig state bindings
        all_mod_set = S.fromList mb_modname
        mod_name = nameModule (idName entry_f)
    hpc_t <- hpcTracker state' all_mod_set (hpc_print_times config) (hpc_print_ticks config)
    let 
        simplifier = FloatSimplifier :>> ArithSimplifier :>> BoolSimplifier :>> StringSimplifier :>> EqualitySimplifier :>> CharConc
        --exp_env_names = E.keys . E.filterConcOrSym (\case { E.Sym _ -> False; E.Conc _ -> True }) $ expr_env state
        callGraph = G.getCallGraph $ expr_env state'
        reachable_funcs = G.reachable (idName entry_f) callGraph

        executable_funcs = case check_asserts config of
                                False -> getFuncsByModule mb_modname reachable_funcs
                                True -> getFuncsByAssert callGraph reachable_funcs

        non_rec_funcs = filter (G.isFuncNonRecursive callGraph) reachable_funcs

    analysis1 <- if states_at_time config then do l <- logStatesAtTime; return [l] else return noAnalysis
    let analysis2 = if states_at_step config then [\s p xs -> SM.lift .  SM.lift . SM.lift . SM.lift . SM.lift  $ logStatesAtStep s p xs] else noAnalysis
        analysis3 = if print_num_red_rules config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift . SM.lift . SM.lift $ logRedRuleNum s p xs] else noAnalysis
        analysis = analysis1 ++ analysis2 ++ analysis3

    (in_out, bindings'', timed_out) <- case null analysis of
        True -> do
            rho <- initRedHaltOrd state' all_mod_set solver simplifier config (S.fromList executable_funcs) (S.fromList non_rec_funcs)
            case rho of
                (red, hal, ord, to) ->
                        SM.evalStateT (
                            SM.evalStateT
                                (SM.evalStateT
                                    (SM.evalStateT
                                        (SM.evalStateT
                                                (addTimedOut to $ runG2WithValidate proj src (T.unpack $ fromJust mod_name) f entry_f gflags red hal ord [] solver simplifier state' config bindings')
                                            emptyApproxPrevs
                                        )
                                        lnt
                                    )
                                    (if showType config == Lax 
                                    then (mkPrettyGuide ())
                                    else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
                                )
                                hpc_t
                            )
                            HM.empty
        False -> do
            rho <- initRedHaltOrd state' all_mod_set solver simplifier config (S.fromList executable_funcs) (S.fromList non_rec_funcs)
            case rho of
                (red, hal, ord, to) ->
                        SM.evalStateT (
                            SM.evalStateT (
                                SM.evalStateT (
                                    SM.evalStateT
                                        (SM.evalStateT
                                            (SM.evalStateT
                                                (SM.evalStateT
                                                        (addTimedOut to $ runG2WithValidate proj src (T.unpack $ fromJust mod_name) f entry_f gflags red hal ord analysis solver simplifier state' config bindings')
                                                    emptyApproxPrevs
                                                )
                                                lnt
                                            )
                                            (if showType config == Lax 
                                            then (mkPrettyGuide ())
                                            else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
                                        )
                                        hpc_t
                                    )
                                    HM.empty
                                )
                                logStatesAtStepTracker
                            )
                            0
                        

    close solver

    return (in_out, bindings'', timed_out)

addTimedOut :: MonadIO m => IORef TimedOut -> m (a, b) -> m (a, b, TimedOut)
addTimedOut to m = do
    (er, b) <- m
    to' <- liftIO $ readIORef to
    return (er, b, to')

getFuncsByModule :: [Maybe T.Text] -> [Name] -> [Name]
getFuncsByModule ms reachable_funcs = 
    let 
        j_ms = filter isJust ms
    in 
    filter (\x -> nameModule x `elem` j_ms) reachable_funcs

getFuncsByAssert :: G.CallGraph -> [Name] -> [Name]
getFuncsByAssert g reachable_funcs = 
    let
        assert_name = L.find (\x -> nameOcc x == "assert" && nameModule x == Just "G2.Symbolic") reachable_funcs
        exec_funcs = case assert_name of
                        Just a -> a : G.getAllCalledBys a g -- Added assert function name too because we want to execute that as well
                        Nothing -> []
    in
        exec_funcs

{-# SPECIALIZE 
    runG2WithSomes :: ( Solver solver
                      , Simplifier simplifier)
                => SomeReducer (RHOStack IO ()) ()
                -> SomeHalter (RHOStack IO ()) (ExecRes ()) ()
                -> SomeOrderer (RHOStack IO ()) (ExecRes ()) ()
                -> [AnalyzeStates (RHOStack IO ()) (ExecRes ()) ()]
                -> solver
                -> simplifier
                -> MemConfig
                -> State ()
                -> Bindings
                -> RHOStack IO () ([ExecRes ()], Bindings)
    #-}
runG2WithSomes :: ( MonadIO m
                  , Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver
                  , Simplifier simplifier)
               => SomeReducer m t
               -> SomeHalter m (ExecRes t) t
               -> SomeOrderer m (ExecRes t) t
               -> [AnalyzeStates m (ExecRes t) t]
               -> solver
               -> simplifier
               -> MemConfig
               -> State t
               -> Bindings
               -> m ([ExecRes t], Bindings)
runG2WithSomes red hal ord analyze solver simplifier mem state bindings =
    case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') ->
            runG2 red' hal' ord' analyze solver simplifier mem state bindings
 
runG2WithSomes' :: ( MonadIO m
                  , Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver
                  , Simplifier simplifier)
               => SomeReducer m t
               -> SomeHalter m (ExecRes t) t
               -> SomeOrderer m (ExecRes t) t
               -> [AnalyzeStates m (ExecRes t) t]
               -> solver
               -> simplifier
               -> State t
               -> Bindings
               -> m ([ExecRes t], Bindings)
runG2WithSomes' red hal ord analyze solver simplifier state bindings =
    case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') ->
            --runG2 red' hal' ord' analyze solver simplifier state bindings
            runExecution red' hal' ord' (runG2Solving solver simplifier) analyze state bindings

runG2WithValidate :: ( MonadIO m
                  , ExceptionMonad m
                  , Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver
                  , Simplifier simplifier)
               => [FilePath]
               -> [FilePath]
               -> String
               -> String
               -> Id
               -> [GeneralFlag]
               -> SomeReducer m t
               -> SomeHalter m (ExecRes t) t
               -> SomeOrderer m (ExecRes t) t
               -> [AnalyzeStates m (ExecRes t) t]
               -> solver
               -> simplifier
               -> State t
               -> Config
               -> Bindings
               -> m ([ExecRes t], Bindings)
runG2WithValidate proj src modN entry entry_id gflags red hal ord analyze solver simplifier state config bindings =
    runGhcT (Just libdir) (case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') -> do
            --runG2 red' hal' ord' analyze solver simplifier state bindings
            let liftGhcT3 f x y z = liftGhcT (f x y z) 
                analyze' = map liftGhcT3 analyze
            runExecution (liftReducerGhcT red') (liftHalterGhcT hal') (liftOrdererGhcT ord') (runG2SolvingValidate proj src modN entry entry_id gflags config solver simplifier) analyze' state bindings)

runG2Pre :: ( Named t
            , ASTContainer t Expr
            , ASTContainer t Type) => MemConfig -> State t -> Bindings -> (State t, Bindings)
runG2Pre mem s bindings =
    let
        swept = markAndSweepPreserving mem s bindings
    in
    runPreprocessing swept bindings

runG2Post :: ( MonadIO m
             , Named t
             , ASTContainer t Expr
             , ASTContainer t Type
             , Solver solver
             , Simplifier simplifier
             , Ord b) => Reducer m rv t -> Halter m hv (ExecRes t) t -> Orderer m sov b (ExecRes t) t ->
             solver -> simplifier -> State t -> Bindings -> m ([ExecRes t], Bindings)
runG2Post red hal ord solver simplifier is bindings = do
    runExecution red hal ord (runG2Solving solver simplifier) [] is bindings

runG2SolvingResult :: ( Named t
                      , Solver solver
                      , Simplifier simplifier) =>
                      solver
                   -> simplifier
                   -> Bindings
                   -> State t
                   -> IO (Result (ExecRes t) () ())
runG2SolvingResult solver simplifier bindings s
    | true_assert s = do
        r <- solve solver s bindings (E.symbolicIds . expr_env $ s) (path_conds s)
        case r of
            SAT m -> do
                let m' = reverseSimplification simplifier s bindings m
                return . SAT $ runG2SubstModel m' s bindings
            UNSAT _ -> return $ UNSAT ()
            Unknown reason _ -> return $ Unknown reason ()

    | otherwise = return $ UNSAT ()

runG2Solving :: ( MonadIO m
                , Named t
                , Solver solver
                , Simplifier simplifier) =>
                solver
             -> simplifier
             -> State t
             -> Bindings
             -> m (Maybe (ExecRes t))
runG2Solving solver simplifier s bindings = do
    res <- liftIO $ runG2SolvingResult solver simplifier bindings s
    case res of
        SAT m -> return $ Just m
        _ -> return Nothing

runG2SolvingValidate :: ( MonadIO m
                        , GhcMonad m
                        , Named t
                        , Solver solver
                        , Simplifier simplifier) =>
                [FilePath]
             -> [FilePath]
             -> String
             -> String
             -> Id
             -> [GeneralFlag]
             -> Config
             -> solver
             -> simplifier
             -> State t
             -> Bindings
             -> m (Maybe (ExecRes t))
runG2SolvingValidate proj src modN entry entry_id gflags config solver simplifier s bindings = do
    loadSession proj src modN gflags
    res <- runG2Solving solver simplifier s bindings
    when (validate config) (
        case res of
            Just m -> do 
                r <- validateState modN entry [] [] bindings m
                liftIO $ printStateOutput config entry_id bindings (Just r) m
            Nothing -> return () 
        )
    return res


runG2SubstModel :: Named t =>
                      Model
                   -> State t
                   -> Bindings
                   -> ExecRes t
runG2SubstModel m s@(State { expr_env = eenv, type_env = tenv, tyvar_env = tv_env, known_values = kv }) bindings =
    let
        s' = s { model = m }

        Subbed { s_inputs = es
               , s_output = e
               , s_violated = ais
               , s_sym_gens = gens
               , s_mutvars = mv
               , s_handles = h } = subModel s' bindings

        sm = ExecRes { final_state = s'
                     , conc_args = es
                     , conc_out = e
                     , conc_sym_gens = gens
                     , conc_mutvars = mv
                     , conc_handles = h
                     , violated = ais}

        sm' = runPostprocessing bindings sm

        sm'' = ExecRes { final_state = final_state sm'
                       , conc_args = fixed_inputs bindings ++ evalPrims eenv tenv tv_env kv (conc_args sm')
                       , conc_out = evalPrims eenv tenv tv_env kv (conc_out sm')
                       , conc_sym_gens = gens
                       , conc_mutvars = mv
                       , conc_handles = conc_handles sm'
                       , violated = evalPrims eenv tenv tv_env kv (violated sm')}
    in
    sm''

{-# SPECIALIZE runG2 :: ( Solver solver
                        , Simplifier simplifier
                        , Ord b) => Reducer (RHOStack IO ()) rv () -> Halter (RHOStack IO ()) hv (ExecRes ()) () -> Orderer (RHOStack IO ()) sov b (ExecRes ()) () ->
                        [AnalyzeStates (RHOStack IO ()) (ExecRes ()) ()] ->
                        solver -> simplifier -> MemConfig -> State () -> Bindings -> RHOStack IO () ([ExecRes ()], Bindings)
    #-}


-- | Runs G2, returning both fully executed states,
-- and states that have only been partially executed.
runG2 :: ( MonadIO m
         , Named t
         , ASTContainer t Expr
         , ASTContainer t Type
         , Solver solver
         , Simplifier simplifier
         , Ord b) => Reducer m rv t -> Halter m hv (ExecRes t) t -> Orderer m sov b (ExecRes t) t -> [AnalyzeStates m (ExecRes t) t] ->
         solver -> simplifier -> MemConfig -> State t -> Bindings -> m ([ExecRes t], Bindings)
runG2 red hal ord analyze solver simplifier mem is bindings = do
    let (is', bindings') = runG2Pre mem is bindings
    runExecution red hal ord (runG2Solving solver simplifier) analyze is' bindings'