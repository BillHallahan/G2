{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Interface ( initState
                              , run
                              , Config) where

import G2.Internals.Config.Config

import G2.Internals.Language

import G2.Internals.Initialization.Interface
import G2.Internals.Initialization.KnownValues
import G2.Internals.Initialization.MkCurrExpr
import qualified G2.Internals.Initialization.Types as IT

import G2.Internals.Preprocessing.Interface

import G2.Internals.Execution.Interface
import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Execution.PrimitiveEval
import G2.Internals.Execution.Memory

import G2.Internals.Solver.Interface

import G2.Internals.Postprocessing.Interface

import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import qualified G2.Internals.Language.Stack as Stack
import qualified G2.Internals.Language.SymLinks as Sym

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
    , arbValueGen = arbValueInit
    , known_values = kv'
    , cleaned_names = M.empty
    , rules = []
    , track = ()
    , tags = S.empty
 }
 , ie)

mkExprEnv :: Program -> E.ExprEnv
mkExprEnv = E.fromExprList . map (\(i, e) -> (idName i, e)) . concat

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, dcs) -> (n, dcs))


run :: (Named hv, Show t
       , Named t
       , ASTContainer hv Expr
       , ASTContainer t Expr
       , ASTContainer hv Type
       , ASTContainer t Type
       , Reducer r t
       , Halter h hv t
       , Orderer or orv sov t
       , Solver solver) => r -> h -> or ->
    solver -> [Name] -> Config -> State t -> IO [(State t, [Expr], Expr, Maybe FuncCall)]
run red hal ord con pns config (is@State { type_env = tenv
                                             , known_values = kv
                                             , apply_types = at
                                             , type_classes = tc }) = do
    let swept = markAndSweepPreserving (pns ++ names at ++ names (lookupStructEqDicts kv tc)) is

    let preproc_state = runPreprocessing swept

    let ior = initOrder ord config preproc_state

    exec_states <- runExecution red hal ord ior [preproc_state] config

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
