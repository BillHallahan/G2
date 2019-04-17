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
                              
                              , initialStateFromFileSimple
                              , initialStateFromFile

                              , runG2FromFile
                              , runG2WithConfig
                              , runG2WithSomes
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

type AssumeFunc = T.Text
type AssertFunc = T.Text
type ReachFunc = T.Text

type StartFunc = T.Text
type ModuleName = Maybe T.Text 

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

initState :: ExtractedG2 -> Maybe AssumeFunc
          -> Maybe AssertFunc -> Bool -> StartFunc -> ModuleName
          -> Config -> (State (), Id, Bindings)
initState exg2 m_assume m_assert useAssert f m_mod config =
    let
        s = initSimpleState exg2
    in
    initStateFromSimpleState s m_assume m_assert useAssert f m_mod config

initState' :: ExtractedG2
           -> StartFunc
           -> ModuleName
           -> Config
           -> (State (), Id, Bindings)
initState' exg2 =
    initState exg2 Nothing Nothing False

initStateFromSimpleState :: IT.SimpleState
                         -> Maybe AssumeFunc
                         -> Maybe AssertFunc
                         -> Bool
                         -> StartFunc
                         -> ModuleName
                         -> Config
                         -> (State (), Id, Bindings)
initStateFromSimpleState s m_assume m_assert useAssert f m_mod config =
    let
        (ie, fe) = case findFunc f m_mod (IT.expr_env s) of
              Left ie' -> ie'
              Right errs -> error errs
        (_, ts) = instantiateArgTypes (IT.type_classes s) (IT.known_values s) fe

        (s', ft, at, ds_walkers) = runInitialization s ts (S.fromList $ IT.exports s)
        eenv' = IT.expr_env s'
        tenv' = IT.type_env s'
        ng' = IT.name_gen s'
        kv' = IT.known_values s'
        tc' = IT.type_classes s'

        (ce, is, f_i, ng'') = mkCurrExpr m_assume m_assert (idName ie) m_mod tc' ng' eenv' ds_walkers kv' config
    in
    (State {
      expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) eenv' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , path_conds = PC.fromList kv' $ map PCExists is
    , non_red_path_conds = []
    , true_assert = if useAssert then False else True
    , assert_ids = Nothing
    , type_classes = tc'
    , symbolic_ids = is
    , exec_stack = Stack.empty
    , model = M.empty
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
    , func_table = ft
    , apply_types = at
    , input_names = map idName is
    , rewrite_rules = IT.rewrite_rules s
    , name_gen = ng''})

initStateFromSimpleState' :: IT.SimpleState
                          -> StartFunc
                          -> ModuleName
                          -> Config
                          -> (State (), Id, Bindings)
initStateFromSimpleState' s=
    initStateFromSimpleState s Nothing Nothing False

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
                          , type_env = tenv
                          , known_values = kv }) m_mod reaches =
    s {expr_env = checkReaches eenv tenv kv reaches m_mod }

initRedHaltOrd :: Solver conv => conv -> Config -> (SomeReducer (), SomeHalter (), SomeOrderer ())
initRedHaltOrd conv config =
    let
        tr_ng = mkNameGen ()
        state_name = Name "state" Nothing 0 Nothing
    in
    if higherOrderSolver config == AllFuncs
        then (SomeReducer (NonRedPCRed)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed conv :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed conv))
             , SomeHalter
                 (SwitchEveryNHalter 20
                 :<~> MaxOutputsHalter (maxOutputs config)
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ PickLeastUsedOrderer)
        else ( SomeReducer (NonRedPCRed :<~| TaggerRed state_name tr_ng)
                 <~| (case logStates config of
                        Just fp -> SomeReducer (StdRed conv :<~ Logger fp)
                        Nothing -> SomeReducer (StdRed conv))
             , SomeHalter
                 (DiscardIfAcceptedTag state_name
                 :<~> SwitchEveryNHalter 20
                 :<~> MaxOutputsHalter (maxOutputs config) 
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ PickLeastUsedOrderer)

initSolver :: Config -> IO SomeSolver
initSolver config = do
    SomeSMTSolver con <- getSMT config
    let con' = GroupRelated (ADTSolver :?> con)
    return (SomeSolver con')

mkExprEnv :: [(Id, Expr)] -> E.ExprEnv
mkExprEnv = E.fromExprList . map (\(i, e) -> (idName i, e))

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, dcs) -> (n, dcs))

initialStateFromFileSimple :: FilePath
                   -> FilePath
                   -> [FilePath]
                   -> StartFunc
                   -> Config
                   -> IO (State (), Id, Bindings)
initialStateFromFileSimple proj src libs f config =
    initialStateFromFile proj src libs Nothing Nothing Nothing False f config

initialStateFromFile :: FilePath
                     -> FilePath
                     -> [FilePath]
                     -> Maybe AssumeFunc
                     -> Maybe AssertFunc
                     -> Maybe ReachFunc
                     -> Bool
                     -> StartFunc
                     -> Config
                     -> IO (State (), Id, Bindings)
initialStateFromFile proj src libs m_assume m_assert m_reach def_assert f config = do
    (mb_modname, exg2) <- translateLoaded proj src libs simplTranslationConfig config
    let (init_s, ent_f, bindings) = initState exg2 m_assume m_assert def_assert
                                    f mb_modname config
        reaches_state = initCheckReaches init_s mb_modname m_reach

    return (reaches_state, ent_f, bindings)

runG2FromFile :: FilePath
              -> FilePath
              -> [FilePath]
              -> Maybe AssumeFunc
              -> Maybe AssertFunc
              -> Maybe ReachFunc
              -> Bool
              -> StartFunc
              -> Config
              -> IO (([ExecRes ()], Bindings), Id)
runG2FromFile proj src libs m_assume m_assert m_reach def_assert f config = do
    (init_state, entry_f, bindings) <- initialStateFromFile proj src libs m_assume
                                    m_assert m_reach def_assert f config

    r <- runG2WithConfig init_state config bindings

    return (r, entry_f)

runG2WithConfig :: State () -> Config -> Bindings -> IO ([ExecRes ()], Bindings)
runG2WithConfig state config bindings = do
    SomeSolver con <- initSolver config

    (in_out, bindings') <- case initRedHaltOrd con config of
                (red, hal, ord) ->
                    runG2WithSomes red hal ord con [] state bindings

    close con

    return (in_out, bindings')

runG2WithSomes :: ( Named t
                  , ASTContainer t Expr
                  , ASTContainer t Type
                  , Solver solver)
               => (SomeReducer t)
               -> (SomeHalter t)
               -> (SomeOrderer t)
               -> solver
               -> [Name]
               -> State t
               -> Bindings
               -> IO ([ExecRes t], Bindings)
runG2WithSomes red hal ord con pns state bindings =
    case (red, hal, ord) of
        (SomeReducer red', SomeHalter hal', SomeOrderer ord') ->
            runG2 red' hal' ord' con pns state bindings

-- | Runs G2, returning both fully executed states,
-- and states that have only been partially executed.
runG2 :: ( Named t
         , ASTContainer t Expr
         , ASTContainer t Type
         , Reducer r rv t
         , Halter h hv t
         , Orderer or sov b t
         , Solver solver) => r -> h -> or ->
         solver -> [Name] -> State t -> Bindings -> IO ([ExecRes t], Bindings)
runG2 red hal ord con pns (is@State { type_env = tenv
                                    , known_values = kv
                                    , type_classes = tc }) 
                          (bindings@Bindings { apply_types = at}) = do
    let (swept, bindings') = markAndSweepPreserving (pns ++ names at ++ names (lookupStructEqDicts kv tc)) is bindings

    let (preproc_state, bindings'') = runPreprocessing swept bindings'

    (exec_states, bindings''') <- runExecution red hal ord preproc_state bindings''

    let ident_states = filter true_assert exec_states

    ident_states' <- 
        mapM (\s -> do
            (_, m) <- solve con s bindings''' (symbolic_ids s) (path_conds s)
            return . fmap (\m' -> s {model = m'}) $ m
            ) $ ident_states

    let ident_states'' = catMaybes ident_states'

    let sm = map (\s -> 
              let (es, e, ais) = subModel s bindings''' in
                ExecRes { final_state = s
                        , conc_args = es
                        , conc_out = e
                        , violated = ais}) $ ident_states''

    let sm' = map (\sm''@(ExecRes {final_state = s}) -> 
                                   runPostprocessing s bindings''' sm'') sm

    let sm'' = map (\ExecRes { final_state = s
                             , conc_args = es
                             , conc_out = e
                             , violated = ais} ->
                                  ExecRes { final_state = s
                                          , conc_args = fixed_inputs bindings''' ++ es
                                          , conc_out = evalPrims kv tenv e
                                          , violated = evalPrims kv tenv ais}) sm'

    return (sm'', bindings''')
