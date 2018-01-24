module G2.Internals.Interface ( initState
                              , addPolyPred
                              , addHigherOrderWrappers
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

import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import qualified G2.Internals.Language.Stack as Stack
import qualified G2.Internals.Language.SymLinks as Sym

import Debug.Trace as T

import qualified Data.Map as M
import Data.Maybe

import G2.Lib.Printers

initState :: Program -> [ProgramType] -> [(Name, Id)] -> Maybe String -> Maybe String -> Maybe String -> Bool -> String -> State
initState prog prog_typ cls m_assume m_assert m_reaches useAssert f =
    let
        eenv = mkExprEnv prog
        tenv = mkTypeEnv prog_typ
        ng = mkNameGen prog prog_typ

        (eenv', tenv', ng', ft, at, ds_walkers, pt_walkers, wrap, kv) = runInitialization eenv tenv ng

        (ce, is, ng'') = mkCurrExpr m_assume m_assert f at ng' eenv' ds_walkers kv

        eenv'' = checkReaches eenv' tenv' kv m_reaches
    in
    State {
      expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) eenv'' is
    , type_env = tenv'
    , curr_expr = CurrExpr Evaluate ce
    , name_gen =  ng''
    , path_conds = PC.fromList kv $ map PCExists is
    , true_assert = if useAssert then False else True
    , assert_ids = Nothing
    , type_classes = initTypeClasses cls
    , input_ids = is
    , sym_links = Sym.empty
    , func_table = ft
    , deepseq_walkers = ds_walkers
    , polypred_walkers = pt_walkers
    , wrappers = wrap
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


-- TODO: Move addPolyPreds and addHigherOrderWrappers elsewhere (somewhere
-- specific to LH?)
addPolyPred :: State -> Name -> Id -> Int -> State
addPolyPred s@(State { expr_env = eenv
                     , polypred_walkers = ppw
                     , known_values = kv}) f fw argN =
    let
        e = eenv E.! f
        i@(Id _ (TyConApp n _)) = nthArg e argN

        wf = M.lookup n ppw

        d = fmap (\wf' -> App (App (App (Var wf') (Type (tyInt kv))) (Var fw)) (Var i)) wf
        e' = case d of
            Just d' -> insertInLams (\_ -> Assume d')  e
            Nothing -> e
    in
    s {expr_env = E.insert f e' eenv}

addHigherOrderWrappers :: State -> Name -> Id -> Int -> State
addHigherOrderWrappers s@(State { expr_env = eenv, wrappers = w }) f fw argN =
    let
        e = eenv E.! f
        i@(Id _ t) = nthArg e argN

        wf = lookup t w

        e' = case wf of
            Just wf' -> replaceASTs (Var i) (App (App (Var wf') (Var fw)) (Var i)) e
            Nothing -> e
    in
    s {expr_env = E.insert f e' eenv}

run :: SMTConverter ast out io -> io -> Int -> State -> IO [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))]
run con hhp n (state@ State { type_env = tenv
                            , known_values = kv }) = do
    -- timedMsg "fuck"
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

    let ident_states = filter (isExecValueForm . snd) exec_states
    let ident_states' = filter (true_assert . snd) ident_states
    let nonident_states = filter (not . isExecValueForm . snd) exec_states

    -- putStrLn $ "exec states: " ++ (show $ length exec_states)
    -- putStrLn $ "ident states: " ++ (show $ length ident_states')

    -- sm <- satModelOutputs con hhp exec_states
    -- let ident_states' = ident_states

    -- mapM_ (\(rs, st) -> do
    --     putStrLn $ show rs
    --     putStrLn $ pprExecStateStr st
    --     -- putStrLn $ pprExecStateStrSimple st

    -- --     -- putStrLn . pprExecEEnvStr $ expr_env st
    --     -- print $ curr_expr st
    -- --     -- print $ true_assert st
    -- --     -- print $ assertions st
    --     -- putStrLn . pprPathsStr . PC.toList $ path_conds st
    -- --     -- print $ E.symbolicKeys $ expr_env st
    -- --     -- print $ input_ids st
    -- --     -- print $ model st
    --     putStrLn "----\n"
    --     ) exec_states


    ident_states'' <- 
        mapM (\(r, s) -> do
            (_, m) <- checkModel con hhp s
            return . fmap (\m' -> (r, s {model = m'})) $ m
            ) $ ident_states'

    let ident_states''' = catMaybes ident_states''

    let sm = map (\(r, s) -> let (es, e, ais) = subModel s in (s, r, es, e, ais)) $ ident_states'''


    let sm' = map (\(s, r, es, e, ais) -> (s, r, es, evalPrims kv tenv e, ais)) sm

    return $ map (\sm''@(s, _, _, _, _) -> runPostprocessing s sm'') sm'
