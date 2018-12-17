{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Interface ( initState
                              , initRedHaltOrd
                              , runG2WithConfig
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

import G2.Solver

import G2.Postprocessing.Interface

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stack
import qualified G2.Language.SymLinks as Sym

import qualified Data.HashSet as S
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

initState :: Program -> [ProgramType] -> [(Name, Id, [Id])] -> Maybe T.Text
          -> Maybe T.Text -> Maybe T.Text -> Bool -> T.Text -> Maybe T.Text -> [Name]
          -> Config -> (State (), Id)
initState prog prog_typ cls m_assume m_assert m_reaches useAssert f m_mod tgtNames config =
    let
        eenv = mkExprEnv prog
        tenv = mkTypeEnv prog_typ
        tc = initTypeClasses cls
        kv = initKnownValues eenv tenv

        (ie, fe) = case findFunc f m_mod eenv of
              Left ie' -> ie'
              Right s -> error s
        (_, ts) = instantiateArgTypes tc kv fe

        ng = mkNameGen (prog, prog_typ)

        (s', ft, at, ds_walkers) = runInitialization eenv tenv ng kv tc ts tgtNames
        eenv' = IT.expr_env s'
        tenv' = IT.type_env s'
        ng' = IT.name_gen s'
        kv' = IT.known_values s'
        tc' = IT.type_classes s'

        (ce, is, f_i, ng'') = mkCurrExpr m_assume m_assert f m_mod tc ng' eenv' ds_walkers kv config

        eenv'' = checkReaches eenv' tenv' kv m_reaches m_mod
    in
    (State {
      expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) eenv'' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , name_gen =  ng''
    , path_conds = PC.fromList kv $ map PCExists is
    , non_red_path_conds = []
    , true_assert = if useAssert then False else True
    , assert_ids = Nothing
    , type_classes = tc'
    , input_ids = is
    , fixed_inputs = f_i
    , symbolic_ids = is
    , sym_links = Sym.empty
    , func_table = ft
    , deepseq_walkers = ds_walkers
    , apply_types = at
    , exec_stack = Stack.empty
    , model = M.empty
    , arb_value_gen = arbValueInit
    , known_values = kv'
    , cleaned_names = M.empty
    , rules = []
    , num_steps = 0
    , track = ()
    , tags = S.empty
 }
 , ie)

initRedHaltOrd :: Solver conv => conv -> Config -> (SomeReducer (), SomeHalter (), SomeOrderer ())
initRedHaltOrd conv config =
    let
        tr_ng = mkNameGen ()
        state_name = Name "state" Nothing 0 Nothing
    in
    if higherOrderSolver config == AllFuncs
        then ( SomeReducer
                 (NonRedPCRed
                 :<~| StdRed conv)
             , SomeHalter
                 (MaxOutputsHalter (maxOutputs config)
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ NextOrderer)
        else ( SomeReducer
                 (NonRedPCRed
                 :<~| TaggerRed state_name tr_ng
                 :<~| StdRed conv)
             , SomeHalter
                 (DiscardIfAcceptedTag state_name 
                 :<~> MaxOutputsHalter (maxOutputs config) 
                 :<~> ZeroHalter (steps config)
                 :<~> AcceptHalter)
             , SomeOrderer $ NextOrderer)

mkExprEnv :: Program -> E.ExprEnv
mkExprEnv = E.fromExprList . map (\(i, e) -> (idName i, e)) . concat

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, dcs) -> (n, dcs))

runG2WithConfig :: State () -> Config -> IO [(State (), [Expr], Expr, Maybe FuncCall)]
runG2WithConfig state config = do
    SomeSMTSolver con <- getSMT config
    let con' = GroupRelated (ADTSolver :?> con)

    in_out <- case initRedHaltOrd con' config of
                (SomeReducer red, SomeHalter hal, SomeOrderer ord) -> do
                    runG2 red hal ord con' [] config state

    closeIO con

    return in_out

runG2 :: ( Named t
         , ASTContainer t Expr
         , ASTContainer t Type
         , Reducer r rv t
         , Halter h hv t
         , Orderer or sov b t
         , Solver solver) => r -> h -> or ->
         solver -> [Name] -> Config -> State t -> IO [(State t, [Expr], Expr, Maybe FuncCall)]
runG2 red hal ord con pns config (is@State { type_env = tenv
                                             , known_values = kv
                                             , apply_types = at
                                             , type_classes = tc }) = do
    let swept = markAndSweepPreserving (pns ++ names at ++ names (lookupStructEqDicts kv tc)) is

    let preproc_state = runPreprocessing swept

    exec_states <- runExecution red hal ord config preproc_state

    let ident_states = filter (isExecValueForm . snd) exec_states
    let ident_states' = filter (true_assert . snd) ident_states

    ident_states'' <- 
        mapM (\(_, s) -> do
            (_, m) <- solve con s (symbolic_ids s) (path_conds s)
            return . fmap (\m' -> s {model = m'}) $ m
            ) $ ident_states'

    let ident_states''' = catMaybes ident_states''

    let sm = map (\s -> let (es, e, ais) = subModel s in (s, es, e, ais)) $ ident_states'''

    let sm' = map (\sm''@(s, _, _, _) -> runPostprocessing s sm'') sm

    let sm'' = map (\(s, es, e, ais) -> (s, fixed_inputs s ++ es, evalPrims kv tenv e, evalPrims kv tenv ais)) sm'

    return sm''
