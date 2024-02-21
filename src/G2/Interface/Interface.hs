{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

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
                              , runG2ThroughExecution
                              , runExecution
                              , runG2SolvingResult
                              , runG2Solving
                              , runG2
                              , Config) where

import G2.Config.Config

import G2.Language

import G2.Initialization.Interface
import G2.Initialization.KnownValues
import G2.Initialization.MkCurrExpr
import qualified G2.Initialization.Types as IT

import G2.Preprocessing.Interface

import G2.Execution.Interface
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Execution.PrimitiveEval
import G2.Execution.Memory

import G2.Interface.OutputTypes

import G2.Lib.Printers

import G2.Translation

import G2.Solver

import G2.Postprocessing.Interface

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.Maybe
import qualified Data.Sequence as Seq
import qualified Data.Text as T

import System.Timeout

type AssumeFunc = T.Text
type AssertFunc = T.Text
type ReachFunc = T.Text

type StartFunc = T.Text
type ModuleName = Maybe T.Text 

type MkCurrExpr = TypeClasses -> NameGen -> ExprEnv -> TypeEnv -> Walkers
                     -> KnownValues -> Config -> (Expr, [Id], [Expr], NameGen)

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
                  -> ModuleName
                  -> (Id -> MkCurrExpr)
                  -> (Expr -> MkArgTypes)
                  -> Config
                  -> (State (), Bindings)
initStateWithCall exg2 useAssert f m_mod mkCurr argTys config =
    let
        s = initSimpleState exg2

        (ie, fe) = case findFunc f m_mod (IT.expr_env s) of
                        Left ie' -> ie'
                        Right errs -> error errs
    in
    initStateFromSimpleState s m_mod useAssert (mkCurr ie) (argTys fe) config

{-# INLINE initStateWithCall' #-}
initStateWithCall' :: ExtractedG2
                   -> StartFunc
                   -> ModuleName
                   -> (Id -> MkCurrExpr)
                   -> (Expr -> MkArgTypes)
                   -> Config
                   -> (State (), Bindings)
initStateWithCall' exg2 =
    initStateWithCall exg2 False

{-# INLINE initStateFromSimpleStateWithCall #-}
initStateFromSimpleStateWithCall :: IT.SimpleState
                                 -> Bool
                                 -> StartFunc
                                 -> ModuleName
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
                         -> Maybe T.Text
                         -> Bool
                         -> MkCurrExpr
                         -> MkArgTypes
                         -> Config
                         -> (State (), Bindings)
initStateFromSimpleState s m_mod useAssert mkCurr argTys config =
    let
        (s', ds_walkers) = runInitialization2 s argTys
        eenv' = IT.expr_env s'
        tenv' = IT.type_env s'
        ng' = IT.name_gen s'
        kv' = IT.known_values s'
        tc' = IT.type_classes s'

        (ce, is, f_i, ng'') = mkCurr tc' ng' eenv' tenv' ds_walkers kv' config
    in
    (State {
      expr_env = foldr E.insertSymbolic eenv' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , path_conds = PC.fromList []
    , non_red_path_conds = []
    , true_assert = if useAssert then False else True
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
    deepseq_walkers = ds_walkers
    , fixed_inputs = f_i
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = map idName is
    , higher_order_inst = S.filter (\n -> nameModule n == m_mod) . S.fromList $ IT.exports s
    , rewrite_rules = IT.rewrite_rules s
    , name_gen = ng''
    , exported_funcs = IT.exports s })

mkArgTys :: Expr -> MkArgTypes
mkArgTys e simp_s =
    snd $ instantiateArgTypes (IT.type_classes simp_s) (IT.known_values simp_s) e

{-# INLINE initStateFromSimpleState' #-}
initStateFromSimpleState' :: IT.SimpleState
                          -> StartFunc
                          -> ModuleName
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
                           , IT.known_values = kv
                           , IT.type_classes = tc
                           , IT.rewrite_rules = rs
                           , IT.exports = es }
    in
    runInitialization1 s

initCheckReaches :: State t -> ModuleName -> Maybe ReachFunc -> State t
initCheckReaches s@(State { expr_env = eenv
                          , known_values = kv }) m_mod reaches =
    s {expr_env = checkReaches eenv kv reaches m_mod }

{-# SPECIALIZE 
    initRedHaltOrd :: (Solver solver, Simplifier simplifier) =>
                      solver
                   -> simplifier
                   -> Config
                   -> (SomeReducer (SM.StateT PrettyGuide IO) (), SomeHalter (SM.StateT PrettyGuide IO) (), SomeOrderer ())
    #-}
initRedHaltOrd :: (MonadIO m, Solver solver, Simplifier simplifier) =>
                  solver
               -> simplifier
               -> Config
               -> (SomeReducer (SM.StateT PrettyGuide m) (), SomeHalter (SM.StateT PrettyGuide m) (), SomeOrderer ())
initRedHaltOrd solver simplifier config =
    let
        share = sharing config

        state_name = Name "state" Nothing 0 Nothing

        m_logger = fmap SomeReducer $ getLogger config

        logger_std_red f = case m_logger of
                            Just logger -> logger .~> SomeReducer (stdRed share f solver simplifier)
                            Nothing -> SomeReducer (stdRed share f solver simplifier)
    in
    case higherOrderSolver config of
        AllFuncs ->
            ( logger_std_red retReplaceSymbFuncVar .== Finished .--> SomeReducer nonRedPCRed
             , SomeHalter
                 (switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config)
                 <~> zeroHalter (steps config)
                 <~> acceptIfViolatedHalter)
             , SomeOrderer $ pickLeastUsedOrderer)
        SingleFunc ->
            ( logger_std_red retReplaceSymbFuncVar .== Finished .--> taggerRed state_name :== Finished --> nonRedPCRed
             , SomeHalter
                 (discardIfAcceptedTagHalter state_name
                 <~> switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config) 
                 <~> zeroHalter (steps config)
                 <~> acceptIfViolatedHalter)
             , SomeOrderer $ pickLeastUsedOrderer)
        SymbolicFunc ->
            ( logger_std_red retReplaceSymbFuncTemplate .== Finished .--> SomeReducer nonRedPCRed
             , SomeHalter
                 (switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config)
                 <~> zeroHalter (steps config)
                 <~> acceptIfViolatedHalter)
             , SomeOrderer $ pickLeastUsedOrderer)
        SymbolicFuncTemplate ->
            ( logger_std_red retReplaceSymbFuncVar .== Finished .--> taggerRed state_name :== Finished --> nonRedPCTemplates
             , SomeHalter
                 (discardIfAcceptedTagHalter state_name
                 <~> switchEveryNHalter 20
                 <~> maxOutputsHalter (maxOutputs config) 
                 <~> zeroHalter (steps config)
                 <~> acceptIfViolatedHalter)
             , SomeOrderer $ pickLeastUsedOrderer)

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
                   -> IO (State (), Id, Bindings)
initialStateFromFileSimple proj src f mkCurr argTys config =
    initialStateFromFile proj src Nothing False f mkCurr argTys simplTranslationConfig config

initialStateNoStartFunc :: [FilePath]
                     -> [FilePath]
                     -> TranslationConfig
                     -> Config
                     -> IO (State (), Bindings)
initialStateNoStartFunc proj src transConfig config = do
    (m_mod, exg2) <- translateLoaded proj src transConfig config

    let simp_state = initSimpleState exg2

        (init_s, bindings) = initStateFromSimpleState simp_state m_mod False
                                 (\_ ng _ _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))
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
                     -> IO (State (), Id, Bindings)
initialStateFromFile proj src m_reach def_assert f mkCurr argTys transConfig config = do
    (mb_modname, exg2) <- translateLoaded proj src transConfig config

    let simp_state = initSimpleState exg2
        (ie, fe) = case findFunc f mb_modname (IT.expr_env simp_state) of
                        Left ie' -> ie'
                        Right errs -> error errs

        (init_s, bindings) = initStateFromSimpleState simp_state mb_modname def_assert
                                                  (mkCurr ie) (argTys fe) config
    -- let (init_s, ent_f, bindings) = initState exg2 def_assert
    --                                 f mb_modname mkCurr argTys config
        reaches_state = initCheckReaches init_s mb_modname m_reach

    return (reaches_state, ie, bindings)

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
    (init_state, entry_f, bindings) <- initialStateFromFile proj src
                                    m_reach def_assert f (mkCurrExpr m_assume m_assert) (mkArgTys)
                                    transConfig config

    r <- runG2WithConfig init_state config bindings

    return (r, entry_f)

runG2WithConfig :: State () -> Config -> Bindings -> IO ([ExecRes ()], Bindings)
runG2WithConfig state config bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = IdSimplifier

    (in_out, bindings') <- case initRedHaltOrd solver simplifier config of
                (red, hal, ord) ->
                    SM.evalStateT (runG2WithSomes red hal ord solver simplifier emptyMemConfig state bindings) (mkPrettyGuide ())

    close solver

    return (in_out, bindings')


{-# SPECIALIZE 
    runG2WithSomes :: ( Solver solver
                      , Simplifier simplifier)
                => SomeReducer (SM.StateT PrettyGuide IO) ()
                -> SomeHalter (SM.StateT PrettyGuide IO) ()
                -> SomeOrderer ()
                -> solver
                -> simplifier
                -> MemConfig
                -> State ()
                -> Bindings
                -> SM.StateT PrettyGuide IO ([ExecRes ()], Bindings)
    #-}
runG2WithSomes :: ( MonadIO m
                  , Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver
                  , Simplifier simplifier)
               => SomeReducer m t
               -> SomeHalter m t
               -> SomeOrderer t
               -> solver
               -> simplifier
               -> MemConfig
               -> State t
               -> Bindings
               -> m ([ExecRes t], Bindings)
runG2WithSomes red hal ord solver simplifier mem state bindings =
    case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') ->
            runG2 red' hal' ord' solver simplifier mem state bindings

runG2Pre :: ( Named t
            , ASTContainer t Expr
            , ASTContainer t Type) => MemConfig -> State t -> Bindings -> (State t, Bindings)
runG2Pre mem s bindings =
    let
        (swept, bindings') = markAndSweepPreserving mem s bindings
    in
    runPreprocessing swept bindings'

runG2Post :: ( MonadIO m
             , Named t
             , ASTContainer t Expr
             , ASTContainer t Type
             , Solver solver
             , Simplifier simplifier
             , Ord b) => Reducer m rv t -> Halter m hv t -> Orderer sov b t ->
             solver -> simplifier -> State t -> Bindings -> m ([ExecRes t], Bindings)
runG2Post red hal ord solver simplifier is bindings = do
    (exec_states, bindings') <- runExecution red hal ord is bindings
    sol_states <- mapM (runG2Solving solver simplifier bindings') exec_states

    return (catMaybes sol_states, bindings')

{-# SPECIALISE runG2ThroughExecution ::
    ( Named t
    , ASTContainer t Expr
    , ASTContainer t Type
    , Ord b) => Reducer IO rv t -> Halter IO hv t -> Orderer sov b t ->
    MemConfig -> State t -> Bindings -> IO ([State t], Bindings) #-}
{-# SPECIALISE runG2ThroughExecution ::
    ( Named t
    , ASTContainer t Expr
    , ASTContainer t Type
    , Ord b) => Reducer (SM.StateT PrettyGuide IO) rv t -> Halter (SM.StateT PrettyGuide IO) hv t -> Orderer sov b t ->
    MemConfig -> State t -> Bindings -> SM.StateT PrettyGuide IO ([State t], Bindings) #-}
runG2ThroughExecution ::
    ( Monad m
    , Named t
    , ASTContainer t Expr
    , ASTContainer t Type
    , Ord b) => Reducer m rv t -> Halter m hv t -> Orderer sov b t ->
    MemConfig -> State t -> Bindings -> m ([State t], Bindings)
runG2ThroughExecution red hal ord mem is bindings = do
    let (is', bindings') = runG2Pre mem is bindings
    runExecution red hal ord is' bindings'
{-# INLINABLE runG2ThroughExecution #-}

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
             -> Bindings
             -> State t
             -> m (Maybe (ExecRes t))
runG2Solving solver simplifier bindings s = do
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

        (es, e, ais, gens) = subModel s' bindings
        sm = ExecRes { final_state = s'
                     , conc_args = es
                     , conc_out = e
                     , conc_sym_gens = gens
                     , violated = ais}

        sm' = runPostprocessing bindings sm

        sm'' = ExecRes { final_state = final_state sm'
                       , conc_args = fixed_inputs bindings ++ conc_args sm'
                       , conc_out = evalPrims tenv kv (conc_out sm')
                       , conc_sym_gens = gens
                       , violated = evalPrims tenv kv (violated sm')}
    in
    sm''

-- | Runs G2, returning both fully executed states,
-- and states that have only been partially executed.
runG2 :: ( MonadIO m
         , Named t
         , ASTContainer t Expr
         , ASTContainer t Type
         , Solver solver
         , Simplifier simplifier
         , Ord b) => Reducer m rv t -> Halter m hv t -> Orderer sov b t ->
         solver -> simplifier -> MemConfig -> State t -> Bindings -> m ([ExecRes t], Bindings)
runG2 red hal ord solver simplifier mem is bindings = do
    (exec_states, bindings') <- runG2ThroughExecution red hal ord mem is bindings
    sol_states <- mapM (runG2Solving solver simplifier bindings') exec_states

    return (catMaybes sol_states, bindings')
