{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Interface.Interface ( doTimeout
                              , maybeDoTimeout

                              , initState
                              , initState'
                              , initStateFromSimpleState
                              , initStateFromSimpleState'
                              , initSimpleState
                              
                              , initRedHaltOrd
                              , initSolver
                              , initSolverInfinite
                              
                              , initialStateFromFileSimple
                              , initialStateFromFile

                              , runG2FromFile
                              , runG2WithConfig
                              , runG2WithSomes
                              , runG2Pre
                              , runG2Post
                              , runG2ThroughExecution
                              , runExecution
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
import G2.Execution.PrimitiveEval
import G2.Execution.Memory

import G2.Interface.OutputTypes

import G2.Translation

import G2.Solver

import G2.Postprocessing.Interface

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import System.Timeout

import G2.Lib.Printers

type AssumeFunc = T.Text
type AssertFunc = T.Text
type ReachFunc = T.Text

type StartFunc = T.Text
type ModuleName = Maybe T.Text 

type MkCurrExpr = Id -> TypeClasses -> NameGen -> ExprEnv -> Walkers
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

initState :: ExtractedG2 -> Bool -> StartFunc -> ModuleName
          -> MkCurrExpr
          -> Config -> (State (), Id, Bindings)
initState exg2 useAssert f m_mod mkCurr config =
    let
        s = initSimpleState exg2
    in
    initStateFromSimpleState s useAssert f m_mod mkCurr config

initState' :: ExtractedG2
           -> StartFunc
           -> ModuleName
           -> MkCurrExpr
           -> Config
           -> (State (), Id, Bindings)
initState' exg2 sf m_mod mkCurr =
    initState exg2 False sf m_mod mkCurr

initStateFromSimpleState :: IT.SimpleState
                         -> Bool
                         -> StartFunc
                         -> ModuleName
                         -> MkCurrExpr
                         -> Config
                         -> (State (), Id, Bindings)
initStateFromSimpleState s useAssert f m_mod mkCurr config =
    let
        (ie, fe) = case findFunc f m_mod (IT.expr_env s) of
              Left ie' -> ie'
              Right errs -> error errs
        (_, ts) = instantiateArgTypes (IT.type_classes s) (IT.known_values s) fe

        (s', ds_walkers) = runInitialization s ts
        eenv' = IT.expr_env s'
        tenv' = IT.type_env s'
        ng' = IT.name_gen s'
        kv' = IT.known_values s'
        tc' = IT.type_classes s'

        (ce, is, f_i, ng'') = mkCurr ie tc' ng' eenv' ds_walkers kv' config
    in
    (State {
      expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) eenv' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , path_conds = PC.fromList []
    , non_red_path_conds = []
    , true_assert = if useAssert then False else True
    , assert_ids = Nothing
    , type_classes = tc'
    , symbolic_ids = is
    , exec_stack = Stack.empty
    , model = M.empty
    , adt_int_maps = M.empty
    , simplified = M.empty
    , known_values = kv'
    , rules = []
    , num_steps = 0
    , track = ()
    , tags = S.empty
    }
    , ie
    , Bindings {
    deepseq_walkers = ds_walkers
    , fixed_inputs = f_i
    , arb_value_gen = arbValueInit
    , cleaned_names = HM.empty
    , input_names = map idName is
    , higher_order_inst = IT.exports s
    , rewrite_rules = IT.rewrite_rules s
    , name_gen = ng''})

initStateFromSimpleState' :: IT.SimpleState
                          -> StartFunc
                          -> ModuleName
                          -> Config
                          -> (State (), Id, Bindings)
initStateFromSimpleState' s sf m_mod =
    initStateFromSimpleState s False sf m_mod (mkCurrExpr Nothing Nothing)

initSimpleState :: ExtractedG2
                -> IT.SimpleState
initSimpleState (ExtractedG2 { exg2_binds = prog
                             , exg2_tycons = prog_typ
                             , exg2_classes = cls
                             , exg2_exports = es
                             , exg2_rules = rs }) =
    let
        eenv = mkExprEnv prog
        tenv = mkTypeEnv prog_typ
        tc = initTypeClasses cls
        kv = initKnownValues eenv tenv
        ng = mkNameGen (prog, prog_typ)
    in
    IT.SimpleState { IT.expr_env = eenv
                   , IT.type_env = tenv
                   , IT.name_gen = ng
                   , IT.known_values = kv
                   , IT.type_classes = tc
                   , IT.rewrite_rules = rs
                   , IT.exports = es }

initCheckReaches :: State t -> ModuleName -> Maybe ReachFunc -> State t
initCheckReaches s@(State { expr_env = eenv
                          , known_values = kv }) m_mod reaches =
    s {expr_env = checkReaches eenv kv reaches m_mod }

initRedHaltOrd :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Config -> (SomeReducer (), SomeHalter (), SomeOrderer ())
initRedHaltOrd solver simplifier config =
    let
        share = sharing config

        tr_ng = mkNameGen ()
        state_name = Name "state" Nothing 0 Nothing
    in
    if higherOrderSolver config == AllFuncs
        then (SomeReducer (NonRedPCRed)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed share solver simplifier :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed share solver simplifier))
             , SomeHalter
                 (SwitchEveryNHalter 20
                 :<~> MaxOutputsHalter (maxOutputs config)
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ PickLeastUsedOrderer)
        else ( SomeReducer (NonRedPCRed :<~| TaggerRed state_name tr_ng)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed share solver simplifier :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed share solver simplifier))
             , SomeHalter
                 (DiscardIfAcceptedTag state_name
                 :<~> SwitchEveryNHalter 20
                 :<~> MaxOutputsHalter (maxOutputs config) 
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ PickLeastUsedOrderer)

initSolver :: Config -> IO SomeSolver
initSolver = initSolver' arbValue

initSolverInfinite :: Config -> IO SomeSolver
initSolverInfinite con = initSolver' arbValueInfinite con

initSolver' :: ArbValueFunc -> Config -> IO SomeSolver
initSolver' avf config = do
    SomeSMTSolver con <- getSMTAV avf config
    let con' = GroupRelated avf (UndefinedHigherOrder :?> (ADTNumericalSolver avf con))
    return (SomeSolver con')

mkExprEnv :: [(Id, Expr)] -> E.ExprEnv
mkExprEnv = E.fromExprList . map (\(i, e) -> (idName i, e))

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, dcs) -> (n, dcs))

initialStateFromFileSimple :: [FilePath]
                   -> [FilePath]
                   -> [FilePath]
                   -> StartFunc
                   -> MkCurrExpr
                   -> Config
                   -> IO (State (), Id, Bindings)
initialStateFromFileSimple proj src libs f mkCurr config =
    initialStateFromFile proj src libs Nothing False f mkCurr config

initialStateFromFile :: [FilePath]
                     -> [FilePath]
                     -> [FilePath]
                     -> Maybe ReachFunc
                     -> Bool
                     -> StartFunc
                     -> MkCurrExpr
                     -> Config
                     -> IO (State (), Id, Bindings)
initialStateFromFile proj src libs m_reach def_assert f mkCurr config = do
    (mb_modname, exg2) <- translateLoaded proj src libs simplTranslationConfig config
    let (init_s, ent_f, bindings) = initState exg2 def_assert
                                    f mb_modname mkCurr config
        reaches_state = initCheckReaches init_s mb_modname m_reach

    return (reaches_state, ent_f, bindings)

runG2FromFile :: [FilePath]
              -> [FilePath]
              -> [FilePath]
              -> Maybe AssumeFunc
              -> Maybe AssertFunc
              -> Maybe ReachFunc
              -> Bool
              -> StartFunc
              -> Config
              -> IO (([ExecRes ()], Bindings), Id)
runG2FromFile proj src libs m_assume m_assert m_reach def_assert f config = do
    (init_state, entry_f, bindings) <- initialStateFromFile proj src libs
                                    m_reach def_assert f (mkCurrExpr m_assume m_assert) config

    r <- runG2WithConfig init_state config bindings

    return (r, entry_f)

runG2WithConfig :: State () -> Config -> Bindings -> IO ([ExecRes ()], Bindings)
runG2WithConfig state config bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue

    (in_out, bindings') <- case initRedHaltOrd solver simplifier config of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord solver simplifier [] state bindings

    close solver

    return (in_out, bindings')

runG2WithSomes :: ( Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver
                  , Simplifier simplifier)
               => (SomeReducer t)
               -> (SomeHalter t)
               -> (SomeOrderer t)
               -> solver
               -> simplifier
               -> [Name]
               -> State t
               -> Bindings
               -> IO ([ExecRes t], Bindings)
runG2WithSomes red hal ord solver simplifier pns state bindings =
    case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') ->
            runG2 red' hal' ord' solver simplifier pns state bindings

runG2Pre :: ( Named t
            , ASTContainer t Expr
            , ASTContainer t Type) => [Name] -> State t -> Bindings -> (State t, Bindings)
runG2Pre pns s@(State { known_values = kv, type_classes = tc }) bindings =
    let
        (swept, bindings') = markAndSweepPreserving (pns ++ names (lookupStructEqDicts kv tc)) s bindings
    in
    runPreprocessing swept bindings'

runG2Post :: ( Named t
             , ASTContainer t Expr
             , ASTContainer t Type
             , Reducer r rv t
             , Halter h hv t
             , Orderer or sov b t
             , Solver solver
             , Simplifier simplifier) => r -> h -> or ->
             solver -> simplifier -> State t -> Bindings -> IO ([ExecRes t], Bindings)
runG2Post red hal ord solver simplifier is bindings = do
    (exec_states, bindings') <- runExecution red hal ord is bindings
    sol_states <- mapM (runG2Solving solver simplifier bindings') exec_states

    return (catMaybes sol_states, bindings')

runG2ThroughExecution ::
    ( Named t
    , ASTContainer t Expr
    , ASTContainer t Type
    , Reducer r rv t
    , Halter h hv t
    , Orderer or sov b t) => r -> h -> or ->
    [Name] -> State t -> Bindings -> IO ([State t], Bindings)
runG2ThroughExecution red hal ord pns is bindings = do
    let (is', bindings') = runG2Pre pns is bindings
    runExecution red hal ord is' bindings'

runG2Solving :: ( Named t
                , ASTContainer t Expr
                , ASTContainer t Type
                , Solver solver
                , Simplifier simplifier) =>
                solver -> simplifier -> Bindings -> State t -> IO (Maybe (ExecRes t))
runG2Solving solver simplifier bindings s@(State { known_values = kv })
    | true_assert s = do
        (_, m) <- solve solver s bindings (symbolic_ids s) (path_conds s)
        case m of
            Just m' -> do
                let m'' = reverseSimplification simplifier s bindings m'

                let s' = s { model = m'' }

                let (es, e, ais) = subModel s' bindings
                    sm = ExecRes { final_state = s'
                                 , conc_args = es
                                 , conc_out = e
                                 , violated = ais}

                let sm' = runPostprocessing bindings sm

                let sm'' = ExecRes { final_state = final_state sm'
                                   , conc_args = fixed_inputs bindings ++ conc_args sm'
                                   , conc_out = evalPrims kv (conc_out sm')
                                   , violated = evalPrims kv (violated sm')}
                
                return $ Just sm''
            Nothing -> return Nothing

    | otherwise = return Nothing

-- | Runs G2, returning both fully executed states,
-- and states that have only been partially executed.
runG2 :: ( Named t
         , ASTContainer t Expr
         , ASTContainer t Type
         , Reducer r rv t
         , Halter h hv t
         , Orderer or sov b t
         , Solver solver
         , Simplifier simplifier) => r -> h -> or ->
         solver -> simplifier -> [Name] -> State t -> Bindings -> IO ([ExecRes t], Bindings)
runG2 red hal ord solver simplifier pns is bindings = do
    (exec_states, bindings') <- runG2ThroughExecution red hal ord pns is bindings
    sol_states <- mapM (runG2Solving solver simplifier bindings') exec_states

    return (catMaybes sol_states, bindings')
