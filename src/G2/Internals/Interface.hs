{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Interface ( initState
                              , run) where

import G2.Internals.Language

import G2.Internals.Initialization.Interface
import G2.Internals.Initialization.MkCurrExpr

import G2.Internals.Preprocessing.Interface

import G2.Internals.Execution.Interface
import G2.Internals.Execution.Rules
import G2.Internals.Execution.PrimitiveEval
import G2.Internals.Execution.Memory

import G2.Internals.Solver.Interface
import G2.Internals.Solver.Language hiding (Assert)

import G2.Internals.Postprocessing.Interface

import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import qualified G2.Internals.Language.Stack as Stack
import qualified G2.Internals.Language.SymLinks as Sym

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

initState :: Program -> [ProgramType] -> [(Name, Id, [Id])] -> Maybe T.Text -> Maybe T.Text -> Maybe T.Text -> Bool -> T.Text -> Maybe T.Text -> State
initState prog prog_typ cls m_assume m_assert m_reaches useAssert f m_mod =
    let
        eenv = mkExprEnv prog
        tenv = mkTypeEnv prog_typ
        tc = initTypeClasses cls

        ng = mkNameGen prog prog_typ

        (eenv', tenv', ng', ft, at, ds_walkers, kv) = runInitialization eenv tenv ng

        (ce, is, ng'') = mkCurrExpr m_assume m_assert f m_mod tc at ng' eenv' ds_walkers kv

        eenv'' = checkReaches eenv' tenv' kv m_reaches m_mod
    in
    State {
      expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) eenv'' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , name_gen =  ng''
    , path_conds = PC.fromList kv $ map PCExists is
    , true_assert = if useAssert then False else True
    , assert_ids = Nothing
    , type_classes = tc
    , input_ids = is
    , sym_links = Sym.empty
    , func_table = ft
    , deepseq_walkers = ds_walkers
    , apply_types = at
    , exec_stack = Stack.empty
    , model = M.empty
    , arbValueGen = arbValueInit
    , known_values = kv
    , cleaned_names = M.empty
 }

mkExprEnv :: Program -> E.ExprEnv
mkExprEnv = E.fromExprList . map (\(i, e) -> (idName i, e)) . concat

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, dcs) -> (n, dcs))


run :: SMTConverter ast out io -> io -> Int -> State -> IO [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
run con hhp n (state@ State { type_env = tenv
                            , known_values = kv }) = do
    -- putStrLn . pprExecStateStr $ state
    -- let swept = state

    let swept = markAndSweep state

    -- timedMsg $ "old tenv: " ++ show (M.size $ type_env state)
    -- timedMsg $ "old eenv: " ++ show (E.size $ expr_env state)

    -- timedMsg $ "new tenv: " ++ show (M.size $ type_env swept)
    -- timedMsg $ "new eenv: " ++ show (E.size $ expr_env swept)

    -- timedMsg $ show $ map fst $ M.toList $ type_env swept
    -- timedMsg "--------------------"
    -- timedMsg $ show $ map fst $ E.toList $ expr_env swept



    -- timedMsg "ayo"
    -- putStrLn $ show $ fst $ head $ E.toList $ expr_env swept
    -- putStrLn $ pprExecStateStrSimple swept []
    -- error "we managed to get here at least"
    let preproc_state = runPreprocessing swept


    (_, mdl) <- checkModel con hhp preproc_state

    let preproc_state_alpha = preproc_state { model = fromJust mdl}

    let preproc_state' = preproc_state_alpha

    -- timedMsg "after preprocessing"
    -- putStrLn $ pprExecStateStr preproc_state'
    -- error "this is bad"

    -- putStrLn . pprExecStateStr $ state
    -- putStrLn . pprExecStateStr $ preproc_state'

    -- putStrLn $ "entries in eenv: " ++ (show $ length $ E.keys $ expr_env preproc_state)
    -- putStrLn $ "chars in eenv: " ++ (show $ length $ show $ E.keys $ expr_env preproc_state)
    -- mapM (putStrLn . show) $ E.toList $ expr_env preproc_state
    -- mapM (putStrLn . show) $ zip (take 1 $ E.toList $ expr_env preproc_state) [1..]
    -- mapM (putStrLn . show) $ zip (M.toList $ type_env preproc_state) [1..]
    -- putStrLn $ "chars in eenv: " ++ (show $ expr_env preproc_state)
    -- putStrLn $ "chars in tenv: " ++ (show $ length $ show $ M.keys $ type_env preproc_state)
    -- putStrLn $ pprExecStateStrSimple preproc_state

    -- mapM (putStrLn . show) $ E.keys $ expr_env preproc_state
    -- putStrLn "---------------------------------"
    -- mapM (putStrLn . show) $ M.keys $ type_env preproc_state

    -- putStrLn "^^^^^PREPROCESSED STATE^^^^^"

    exec_states <- runNDepth con hhp [preproc_state'] n

    let list = [ Name "g2Entry3" (Just "Prelude") 8214565720323790643
               -- , Name "walkInt" Nothing 0
               -- , Name "$walk" Nothing 1
               , Name "==" (Just "GHC.Classes") 3458764513820541095
               -- , Name "eqInt" (Just "GHC.Classes") 8214565720323791309
               -- , Name "$+" (Just "GHC.Base") 1
               -- , Name "$-" (Just "GHC.Base") 1
               -- , Name "$*" (Just "GHC.Base") 1
               -- , Name "$fEqInt" (Just "GHC.Classes") 8214565720323785830
               -- , Name "+" (Just "GHC.Num") 8214565720323785390
               -- , Name "$fNumInt" (Just "GHC.Num") 8214565720323786720
               , Name "$fNumInteger" (Just "GHC.Num") 8214565720323796130

               , Name "$fNumFloat" (Just "GHC.Float") 8214565720323796344
               , Name "$fEqFloat" (Just "GHC.Float") 8214565720323796344

               , Name "$c+" Nothing 8214565720323811984
               , Name "$==" Nothing 1
               , Name "fromInteger" (Just "GHC.Num") 8214565720323796906
               , Name "fromIntegerInt" (Just "GHC.Num") 8214565720323796918
               , Name "$cfromInteger" Nothing 8214565720323819153

               , Name "Integer" (Just "GHC.Integer.Type2") 0

               , Name "error" (Just "GHC.Err") 8214565720323791940
               ]

    -- mapM_ (\(rs, s) -> putStrLn $ (show rs) ++ "\n" ++ (pprExecStateStr s)) exec_states
    -- mapM_ (\(rs, s) -> putStrLn $ (show rs) ++ "\n" ++ (pprExecStateStrSimple s list)) exec_states

    let ident_states = filter (isExecValueForm . thd) exec_states
    let ident_states' = filter (true_assert . thd) ident_states
    let nonident_states = filter (not . isExecValueForm . thd) exec_states

    -- putStrLn $ "exec states: " ++ (show $ length exec_states)
    -- putStrLn $ "ident states: " ++ (show $ length ident_states')

    -- sm <- satModelOutputs con hhp exec_states
    -- let ident_states' = ident_states

    -- mapM_ (\(rs, st) -> do
    --     putStrLn $ pprExecStateStr st
    --     putStrLn $ L.intercalate "\n" $ map show $ zip ([1..] :: [Integer]) rs
    -- --     -- putStrLn $ pprExecStateStrSimple st

    -- -- --     -- putStrLn . pprExecEEnvStr $ expr_env st
    -- --     -- print $ curr_expr st
    -- -- --     -- print $ true_assert st
    -- -- --     -- print $ assertions st
    -- --     -- putStrLn . pprPathsStr . PC.toList $ path_conds st
    -- -- --     -- print $ E.symbolicKeys $ expr_env st
    -- -- --     -- print $ input_ids st
    -- -- --     -- print $ model st
    -- --     putStrLn "----\n"
    --     ) exec_states


    ident_states'' <- 
        mapM (\(r, _, s) -> do
            (_, m) <- checkModel con hhp s
            return . fmap (\m' -> (r, s {model = m'})) $ m
            ) $ ident_states'

    let ident_states''' = catMaybes ident_states''

    let sm = map (\(r, s) -> let (es, e, ais) = subModel s in (s, r, es, e, ais)) $ ident_states'''

    let sm' = map (\sm''@(s, _, _, _, _) -> runPostprocessing s sm'') sm
    let sm'' = map (\(s, r, es, e, ais) -> (s, r, es, evalPrims kv tenv e, evalPrims kv tenv ais)) sm'

    return sm''

thd :: (a, b, c) -> c
thd (_, _, x) = x
