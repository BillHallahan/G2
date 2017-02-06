module G2.Core.Utils where

import G2.Core.Language
import G2.Core.Evaluator

import qualified Data.List as L
import qualified Data.Map as M

mkStateStr :: State -> String
mkStateStr (tv, ev, expr, pc) = L.intercalate "\n\n" ["Type Env: " ++ ts, "Expr Env: " ++ es, "Curr Expr: " ++ xs, "Path Constraints: " ++ ps]
  where ts = mkTypeEnvStr tv--show tv
        es = mkExprEnvStr ev
        xs = mkExprStr expr
        ps = show pc

mkStatesStr :: [State] -> String
mkStatesStr []     = ""
mkStatesStr (s:[]) = mkStateStr s
mkStatesStr (s:ss) = mkStateStr s ++ divLn ++ mkStatesStr ss
  where divLn = "\n--------------\n"

mkTypeEnvStr :: TEnv -> String
mkTypeEnvStr t = mkTypeEnvStr' . M.toList $ t
    where
        mkTypeEnvStr' :: [(Name, Type)] -> String
        mkTypeEnvStr' t' = L.intercalate "\n" . map show $ t'

mkExprEnvStr :: EEnv -> String
mkExprEnvStr e = mkExprEnvStr' . M.toList $ e
    where
        mkExprEnvStr' :: [(Name, Expr)] -> String
        mkExprEnvStr' e' = L.intercalate "\n" . map (\(n, e) -> show n ++ ",\n" ++ mkExprStr e) $ e'

mkExprStr :: Expr -> String
mkExprStr e = mkExprStr' e 0
    where
        mkExprStr' :: Expr -> Int -> String
        mkExprStr' (Var n t) i = off i ++ "Var " ++ n ++ " (" ++ mkTypeStr t (i + 1) ++")"
        mkExprStr' l@(Lam n e t) i = off i ++  "Lam (" ++ show n ++ "\n" ++ mkExprStr' e (i + 1) ++ " " ++ mkTypeStr t i ++")"
        mkExprStr' a@(App e1 e2) i = off i ++ "App (\n" ++ mkExprStr' e1 (i + 1) ++ "\n" ++ mkExprStr' e2 (i + 1) ++ "\n" ++ off i ++ ")" 
        mkExprStr' c@(Case e1 ae t) i = off i ++ "Case (\n" ++ mkExprStr' e1 (i + 1) ++ "\n" ++ mkAltExprStr ae (i + 1) ++ " " ++ mkTypeStr t i ++ ")"
        mkExprStr' (Type t) i = off i ++ "Type (" ++ mkTypeStr t (i + 1) ++ ")"
        mkExprStr' x i = off i ++ show x


        mkAltExprStr :: [(Alt, Expr)] -> Int -> String
        mkAltExprStr [] i = ""
        mkAltExprStr ((a, e):xs) i = off i ++ "(" ++ show a ++ ",\n" ++ mkExprStr' e (i + 1) ++ ")" ++ mkAltExprStr xs i

        off :: Int -> String
        off i = duplicate "   " i

mkTypeStr :: Type -> Int -> String
mkTypeStr t i = mkTypeStr' t i False
    where
        mkTypeStr' :: Type -> Int -> Bool -> String
        mkTypeStr' (TyFun t1 t2) i  b = t' t1 t2 "TyFun" i b 
        mkTypeStr' (TyApp t1 t2) i  b = t' t1 t2 "TyApp" i b 
        mkTypeStr' (TyConApp n tx) i b = 
            let li = L.intercalate ", " . map (\t -> mkTypeStr' t (i + 1) b) $ tx in
                off i b ++ "TyConApp " ++ show n ++ "[" ++ li ++ "]"
        mkTypeStr' (TyForAll n t) i b = off i b ++ "TyForAll " ++ show n ++ "(" ++ mkTypeStr' t (i + 1) b ++ ")"
        mkTypeStr' t i b = show t

        t' :: Type -> Type -> String -> Int -> Bool -> String
        t' t1 t2 s i b= off i b ++ s ++ " (" ++ mkTypeStr' t1 (i + 1) True ++ " " ++ mkTypeStr' t2 (i + 1) True ++ off i True ++  ")"

        off :: Int -> Bool -> String
        off i b = if b then "\n" ++ duplicate "   " i else ""

duplicate :: String -> Int -> String
duplicate s 0 = ""
duplicate s n = s ++ duplicate s (n - 1)