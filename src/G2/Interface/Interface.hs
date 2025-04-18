{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE BangPatterns, FlexibleContexts, LambdaCase, OverloadedStrings #-}

module G2.Interface.Interface ( MkCurrExpr
                              , MkArgTypes
                              , IT.SimpleState
                              , doTimeout
                              , maybeDoTimeout

                              , initStateWithCall
                              , initStateWithCall'
                              , initStateFromSimpleState
                              , initStateFromSimpleState'
                              , initStateFromSimpleStateWithCall
                              , initSimpleState

                              , mkArgTys
                              
                              , initRedHaltOrd
                              , initSolver
                              , initSolverInfinite
                              
                              , initialStateFromFileSimple
                              , initialStateFromFile
                              , initialStateNoStartFunc

                              , runG2FromFile
                              , runG2WithConfig
                              , runG2WithSomes
                              , runG2Pre
                              , runG2Post
                              , runExecution
                              , runG2SolvingResult
                              , runG2Solving
                              , runG2
                              , Config) where

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

import G2.Solver

import G2.Postprocessing.Interface

import qualified G2.Language.CallGraph as G
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.Maybe
import Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import qualified Data.List as L
import System.Timeout

type AssumeFunc = T.Text
type AssertFunc = T.Text
type ReachFunc = T.Text

type MkCurrExpr = TypeClasses -> NameGen -> ExprEnv -> TypeEnv
                     -> KnownValues -> Config -> (Expr, [Id], [Expr], Maybe Coercion, NameGen)

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

        (ie, fe) = case findFunc f m_mod (IT.expr_env s) of
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
        (ie, fe) = case findFunc f m_mod (IT.expr_env simp_s) of
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
        (ce, is, f_i, m_coercion, ng'') = mkCurr tc' ng' eenv' tenv' kv' config
    in
    (State {
      expr_env = foldr E.insertSymbolic eenv' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , path_conds = PC.fromList []
    , non_red_path_conds = []
    , handles = hs
    , mutvar_env = HM.empty
    , true_assert = if useAssert || check_asserts config then False else True
    , assert_ids = Nothing
    , type_classes = tc'
    , exec_stack = Stack.empty
    , model = HM.empty
    , known_values = kv'
    , rules = []
    , num_steps = 0
    , track = ()
    , sym_gens = Seq.empty
    , tags = S.empty
    }
    , Bindings {
      fixed_inputs = f_i
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = map idName is
    , input_coercion = m_coercion
    , higher_order_inst = S.filter (\n -> nameModule n `elem` m_mod) . S.fromList $ IT.exports s
    , rewrite_rules = IT.rewrite_rules s
    , name_gen = ng''
    , exported_funcs = IT.exports s })

mkArgTys :: Expr -> MkArgTypes
mkArgTys e simp_s =
    snd $ instantiateArgTypes (IT.type_classes simp_s) (IT.known_values simp_s) e

{-# INLINE initStateFromSimpleState' #-}
initStateFromSimpleState' :: IT.SimpleState
                          -> StartFunc
                          -> [Maybe T.Text]
                          -> Config
                          -> (State (), Bindings)
initStateFromSimpleState' s sf m_mod =
    let
        (ie, fe) = case findFunc sf m_mod (IT.expr_env s) of
                          Left ie' -> ie'
                          Right errs -> error errs
    in
    initStateFromSimpleState s m_mod False (mkCurrExpr Nothing Nothing ie) (mkArgTys fe)

{-# INLINE initSimpleState #-}
initSimpleState :: ExtractedG2
                -> IT.SimpleState
initSimpleState (ExtractedG2 { exg2_binds = prog
                             , exg2_tycons = prog_typ
                             , exg2_classes = cls
                             , exg2_exports = es
                             , exg2_rules = rs }) =
    let
        eenv = E.fromExprMap prog
        tenv = mkTypeEnv prog_typ
        tc = initTypeClasses cls
        kv = initKnownValues eenv tenv tc
        ng = mkNameGen (prog, prog_typ, rs)

        s = IT.SimpleState { IT.expr_env = eenv
                           , IT.type_env = tenv
                           , IT.name_gen = ng
                           , IT.handles = HM.empty
                           , IT.known_values = kv
                           , IT.type_classes = tc
                           , IT.rewrite_rules = rs
                           , IT.exports = es }
    in
    runInitialization1 s

initCheckReaches :: State t -> Maybe T.Text -> Maybe ReachFunc -> State t
initCheckReaches s@(State { expr_env = eenv
                          , known_values = kv }) m_mod reaches =
    s {expr_env = checkReaches eenv kv reaches m_mod }

type RHOStack m = SM.StateT LengthNTrack (SM.StateT PrettyGuide (SM.StateT HpcTracker m))

{-# SPECIALIZE runReducer :: Ord b =>
                             Reducer (RHOStack IO) rv ()
                          -> Halter (RHOStack IO) hv (ExecRes ()) ()
                          -> Orderer (RHOStack IO) sov b (ExecRes ()) ()
                          -> (State () -> Bindings -> RHOStack IO (Maybe (ExecRes ())))
                          -> [AnalyzeStates (RHOStack IO) (ExecRes ()) ()]
                          -> State ()
                          -> Bindings
                          -> (RHOStack IO) (Processed (ExecRes ()) (State ()), Bindings)
    #-}

{-# SPECIALIZE 
    initRedHaltOrd :: (Solver solver, Simplifier simplifier) =>
                      Maybe T.Text
                   -> solver
                   -> simplifier
                   -> Config
                   -> S.HashSet Name
                   -> S.HashSet Name
                   -> S.HashSet Name
                   -> IO (SomeReducer (RHOStack IO) (), SomeHalter (RHOStack IO) (ExecRes ()) (), SomeOrderer (RHOStack IO) (ExecRes ()) ())
    #-}
initRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                  Maybe T.Text
               -> solver
               -> simplifier
               -> Config
               -> S.HashSet Name -- ^ Names of functions that definitely do not lead to symbolic variables in the expr_env
               -> S.HashSet Name -- ^ Names of functions that may not be added to NRPCs
               -> S.HashSet Name -- ^ Names of functions that should not reesult in a larger expression become EXEC,
                                 -- but should not be added to the NRPC at the top level.
               -> IO (SomeReducer (RHOStack m) (), SomeHalter (RHOStack m) (ExecRes ()) (), SomeOrderer (RHOStack m) (ExecRes ()) ())
initRedHaltOrd mod_name solver simplifier config not_symbolic exec_func_names no_nrpc_names = do
    time_logger <- acceptTimeLogger
    time_halter <- stdTimerHalter (fromInteger . toInteger $ timeLimit config)

    let share = sharing config

        state_name = Name "state" Nothing 0 Nothing

        m_logger = fmap SomeReducer $ getLimLogger config

        strict_red f = case strict config of
                            True -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed ~> strictRed)
                            False -> SomeReducer (stdRed share f solver simplifier ~> instTypeRed)

        hpc_red f = case hpc config of
                        True ->  SomeReducer (hpcReducer mod_name) .~> strict_red f 
                        False -> strict_red f

        nrpc_red f = case nrpc config of
                        Nrpc -> liftSomeReducer
                                    (SomeReducer (nonRedLibFuncsReducer
                                                                not_symbolic
                                                                exec_func_names
                                                                no_nrpc_names
                                                                config
                                                 ) .== Finished .--> hpc_red f)
                        NoNrpc -> liftSomeReducer (hpc_red f)

        accept_time_red f = case accept_times config of
                                True -> SomeReducer time_logger .~> nrpc_red f
                                False -> nrpc_red f

        logger_std_red f = case m_logger of
                            Just logger -> liftSomeReducer (logger .~> accept_time_red f)
                            Nothing -> liftSomeReducer (accept_time_red f)

        halter = switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config)
                 <~> acceptIfViolatedHalter
                 <~> time_halter

        halter_step = case step_limit config of
                            True -> SomeHalter (zeroHalter (steps config) <~> halter)
                            False -> SomeHalter halter
        

        orderer = case search_strat config of
                        Subpath -> SomeOrderer $ lengthNSubpathOrderer (subpath_length config)
                        Iterative -> SomeOrderer $ pickLeastUsedOrderer

    return $
        case higherOrderSolver config of
            AllFuncs ->
                ( logger_std_red retReplaceSymbFuncVar .== Finished .--> SomeReducer nonRedPCRed
                ,  halter_step
                , orderer)
            SingleFunc ->
                ( logger_std_red retReplaceSymbFuncVar .== Finished .--> taggerRed state_name :== Finished --> nonRedPCRed
                , SomeHalter (discardIfAcceptedTagHalter state_name) .<~> halter_step
                , orderer)
            SymbolicFunc ->
                ( logger_std_red retReplaceSymbFuncTemplate .== Finished .--> taggerRed state_name :== Finished --> nonRedPCSymFuncRed
                , SomeHalter (discardIfAcceptedTagHalter state_name) .<~> halter_step
                , orderer)

initSolver :: Config -> IO SomeSolver
initSolver = initSolver' arbValue

initSolverInfinite :: Config -> IO SomeSolver
initSolverInfinite con = initSolver' arbValueInfinite con

initSolver' :: ArbValueFunc -> Config -> IO SomeSolver
initSolver' avf config = do
    SomeSMTSolver con <- getSMTAV avf config
    let con' = GroupRelated avf (UndefinedHigherOrder :?> (ADTNumericalSolver avf con))
    return (SomeSolver con')

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
initialStateFromFileSimple proj src f mkCurr argTys config =
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
                                 (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], Nothing, ng))
                                 (E.higherOrderExprs . IT.expr_env)
                                 config

    return (init_s, bindings)

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
        (ie, fe) = case findFunc f mb_modname (IT.expr_env simp_state) of
                        Left ie' -> ie'
                        Right errs -> error errs

        spec_mod = nameModule . idName $ ie

        (init_s, bindings) = initStateFromSimpleState simp_state mb_modname def_assert
                                                  (mkCurr ie) (argTys fe) config
    -- let (init_s, ent_f, bindings) = initState exg2 def_assert
    --                                 f mb_modname mkCurr argTys config
        reaches_state = initCheckReaches init_s spec_mod m_reach

    return (reaches_state, ie, bindings, mb_modname)

runG2FromFile :: [FilePath]
              -> [FilePath]
              -> Maybe AssumeFunc
              -> Maybe AssertFunc
              -> Maybe ReachFunc
              -> Bool
              -> StartFunc
              -> TranslationConfig
              -> Config
              -> IO (([ExecRes ()], Bindings), Id)
runG2FromFile proj src m_assume m_assert m_reach def_assert f transConfig config = do
    (init_state, entry_f, bindings, mb_modname) <- initialStateFromFile proj src
                                    m_reach def_assert f (mkCurrExpr m_assume m_assert) (mkArgTys)
                                    transConfig config

    r <- runG2WithConfig (idName entry_f) mb_modname init_state config bindings

    return (r, entry_f)

runG2WithConfig :: Name -> [Maybe T.Text] -> State () -> Config -> Bindings -> IO ([ExecRes ()], Bindings)
runG2WithConfig entry_f mb_modname state@(State { expr_env = eenv }) config bindings = do
    SomeSolver solver <- initSolver config
    hpc_t <- hpcTracker (hpc_print_times config)
    let 
        (state', bindings') = runG2Pre emptyMemConfig state bindings
        simplifier = FloatSimplifier :>> ArithSimplifier
        --exp_env_names = E.keys . E.filterConcOrSym (\case { E.Sym _ -> False; E.Conc _ -> True }) $ expr_env state
        mod_name = nameModule entry_f
        callGraph = G.getCallGraph $ expr_env state'
        reachable_funcs = G.reachable entry_f callGraph

        executable_funcs = case check_asserts config of
                                False -> getFuncsByModule mb_modname reachable_funcs
                                True -> getFuncsByAssert callGraph reachable_funcs

        non_rec_funcs = filter (isFuncNonRecursive callGraph) reachable_funcs

        not_symbolic = S.fromList
                     . E.keys
                     $ E.filterConcOrSym (\case { E.Conc e -> not (reachesSymbolic S.empty eenv e); E.Sym _ -> False }) eenv

    analysis1 <- if states_at_time config then do l <- logStatesAtTime; return [l] else return noAnalysis
    let analysis2 = if states_at_step config then [\s p xs -> SM.lift . SM.lift . SM.lift $ logStatesAtStep s p xs] else noAnalysis
        analysis3 = if print_num_red_rules config then [\s p xs -> SM.lift . SM.lift . SM.lift . SM.lift $ logRedRuleNum s p xs] else noAnalysis
        analysis4 = if print_nrpcs config then [\s p xs -> SM.lift $ logNRPCs s p xs] else noAnalysis
        analysis = analysis1 ++ analysis2 ++ analysis3 ++ analysis4
    
    (in_out, bindings'') <- case null analysis of
        True -> do
            rho <- initRedHaltOrd mod_name solver simplifier config not_symbolic (S.fromList executable_funcs) (S.fromList non_rec_funcs)
            case rho of
                (red, hal, ord) ->
                        SM.evalStateT
                            (SM.evalStateT
                                (SM.evalStateT
                                    (runG2WithSomes' red hal ord [] solver simplifier state' bindings')
                                    lnt
                                )
                                (if showType config == Lax 
                                then (mkPrettyGuide ())
                                else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
                            )
                            hpc_t
        False -> do
            rho <- initRedHaltOrd mod_name solver simplifier config not_symbolic (S.fromList executable_funcs) (S.fromList non_rec_funcs)
            case rho of
                (red, hal, ord) ->
                    SM.evalStateT (
                        SM.evalStateT (
                            SM.evalStateT
                                (SM.evalStateT
                                    (SM.evalStateT
                                        (runG2WithSomes' red hal ord analysis solver simplifier state' bindings')
                                        lnt
                                    )
                                    (if showType config == Lax 
                                    then (mkPrettyGuide ())
                                    else setTypePrinting AggressiveTypes (mkPrettyGuide ())) 
                                )
                                hpc_t
                            )
                            logStatesAtStepTracker
                        )
                        0

    close solver

    return (in_out, bindings'')

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
                        Just a -> a : getAllCalledBys a g -- Added assert function name too because we want to execute that as well
                        Nothing -> []
    in
        exec_funcs

-- It gives all the methods that call assert function
getAllCalledBys :: Name -> G.CallGraph -> [Name]
getAllCalledBys n g = 
    let
        calledbys = G.calledBy n g
    in
        calledbys ++ concatMap (`getAllCalledBys` g) calledbys

isFuncNonRecursive :: G.CallGraph -> Name -> Bool
isFuncNonRecursive g n = 
    let
        directFuncs = G.calls n g
        reach_funcs = case directFuncs of 
                        Just a -> concatMap (`G.reachable` g) a
                        _ -> []
    in
        not (n `elem` reach_funcs)

{-# SPECIALIZE 
    runG2WithSomes :: ( Solver solver
                      , Simplifier simplifier)
                => SomeReducer (RHOStack IO) ()
                -> SomeHalter (RHOStack IO) (ExecRes ()) ()
                -> SomeOrderer (RHOStack IO) (ExecRes ()) ()
                -> [AnalyzeStates (RHOStack IO) (ExecRes ()) ()]
                -> solver
                -> simplifier
                -> MemConfig
                -> State ()
                -> Bindings
                -> RHOStack IO ([ExecRes ()], Bindings)
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

runG2SubstModel :: Named t =>
                      Model
                   -> State t
                   -> Bindings
                   -> ExecRes t
runG2SubstModel m s@(State { type_env = tenv, known_values = kv }) bindings =
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
                       , conc_args = fixed_inputs bindings ++ conc_args sm'
                       , conc_out = evalPrims tenv kv (conc_out sm')
                       , conc_sym_gens = gens
                       , conc_mutvars = mv
                       , conc_handles = conc_handles sm'
                       , violated = evalPrims tenv kv (violated sm')}
    in
    sm''

{-# SPECIALIZE runG2 :: ( Solver solver
                        , Simplifier simplifier
                        , Ord b) => Reducer (RHOStack IO) rv () -> Halter (RHOStack IO) hv (ExecRes ()) () -> Orderer (RHOStack IO) sov b (ExecRes ()) () ->
                        [AnalyzeStates (RHOStack IO) (ExecRes ()) ()] ->
                        solver -> simplifier -> MemConfig -> State () -> Bindings -> RHOStack IO ([ExecRes ()], Bindings)
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