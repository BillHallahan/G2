module G2.Internals.Interface ( initState
                              , run) where

import G2.Internals.Language

import G2.Internals.Preprocessing.Interface

import G2.Internals.Execution.Interface
import G2.Internals.Execution.Support
import G2.Internals.Execution.Rules

import G2.Internals.SMT.Interface
import G2.Internals.SMT.Language hiding (Assert)

import qualified G2.Internals.Language.SymLinks as Sym

import G2.Lib.Printers

import Data.List
import qualified Data.Map as M

initState :: Program -> [ProgramType] -> Maybe String -> Maybe String -> String -> State
initState prog prog_typ m_assume m_assert f =
    let
        ng = mkNameGen prog
        (ce, ng') = mkCurrExpr m_assume m_assert f ng . concat $ prog
    in
    State {
      expr_env = mkExprEnv . concat $ prog
    , type_env = mkTypeEnv prog_typ
    , curr_expr = ce
    , name_gen = ng'
    , path_conds = []
    , sym_links = Sym.empty
    , func_table = emptyFuncInterps
 }

mkExprEnv :: Binds -> ExprEnv
mkExprEnv = M.fromList . map (\(i, e) -> (idName i, e))

mkTypeEnv :: [ProgramType] -> TypeEnv
mkTypeEnv = M.fromList . map (\(n, ts, dcs) -> (n, AlgDataTy ts dcs))

args :: Type -> [Type]
args (TyFun t ts) = t:args ts  
args _ = []

mkCurrExpr :: Maybe String -> Maybe String -> String -> NameGen -> Binds -> (Expr, NameGen)
mkCurrExpr m_assume m_assert s ng b =
    case findFunc s b of
        Left (f, ex) -> 
            let
                typs = args . typeOf $ ex
                (names, ng') = freshNames (length typs) ng
                ids = map (uncurry Id) $ zip names typs
                var_ids = reverse $ map Var ids
                
                var_ex = Var f
                app_ex = foldr (\vi e -> App e vi) var_ex var_ids

                (name, ng'') = freshName ng'
                id_name = Id name (typeOf f)
                var_name = Var id_name

                assume_ex = mkAssumeAssert Assume m_assume var_ids var_name var_name b
                assert_ex = mkAssumeAssert Assert m_assert var_ids var_name assume_ex b

                
                let_ex = Let [(id_name, app_ex)] assert_ex
            in
            (let_ex, ng'')
        Right s -> error s

mkAssumeAssert :: Primitive -> Maybe String -> [Expr] -> Expr -> Expr -> Binds -> Expr
mkAssumeAssert p (Just f) var_ids inter pre_ex b =
    case findFunc f b of
        Left (f, ex) -> 
            let
                app_ex = foldr (\vi e -> App e vi) (Var f) (pre_ex:var_ids)
                prim_app = App (Prim p) app_ex
            in
            App prim_app inter
        Right s -> error s
mkAssumeAssert _ Nothing _ e _ _ = e

findFunc :: String -> Binds -> Either (Id, Expr) String
findFunc s b = 
    let
        match = filter (\(Id (Name n _ _) _, _) -> n == s) b
    in
    case match of
        [fe] -> Left fe
        x:xs -> Right $ "Multiple functions with name " ++ s
        [] -> Right $ "No functions with name " ++ s


elimNeighboringDups :: Eq a => [a] -> [a]
elimNeighboringDups (x:y:xs) = if x == y then elimNeighboringDups (x:xs) else x:elimNeighboringDups (y:xs)
elimNeighboringDups x = x

run :: SMTConverter ast out io -> io -> Int -> State -> IO [([Expr], Expr)]
run con hhp n state = do
    let preproc_state = runPreprocessing state
    let exec_state = fromState preproc_state
    
    let exec_states = runNDepthHist [exec_state] n

    putStrLn ("\nNumber of states: " ++ (show (length exec_states)))

    let exec_states_error = filter (any (\(r, _) -> r == Just RuleError)) exec_states

    putStrLn ("\nNumber of error states: " ++ (show (length exec_states_error)))

    let red_error = map (reverse . elimNeighboringDups) exec_states_error


    mapM_ (mapM_ (\(r, s) -> do
        putStrLn . show $ r
        putStrLn . show . exec_code $ s
        putStrLn "")) red_error


    return []

    -- let exec_states = runNDepth [exec_state] n
    -- let states = map (toState preproc_state) exec_states
    -- putStrLn ("\nNumber of execution states: " ++ (show (length states)))
    -- ms <- satModelOutputs con hhp states
    -- mapM (\(m, s) -> putStrLn ("Model:\n" ++ show m ++ "\nSMTAST:\n" ++ show s)) ms
    -- return []

{-
run :: SMTConverter ast out io -> io -> Int -> State -> IO [([Expr], Expr)]
run con hhp n state = do
    let preproc_state = runPreprocessing state

    let states = runNDepth [preproc_state] n

    putStrLn ("\nNumber of execution states: " ++ (show (length states)))


    satModelOutputs con hhp states
-}
