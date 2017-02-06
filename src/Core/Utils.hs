module G2.Core.Utils where

import G2.Core.Language
import G2.Core.Evaluator

import qualified Data.List as L
import qualified Data.Map as M

mkStateStr :: State -> String
mkStateStr (tv, ev, expr, pc) = L.intercalate "\n" [ts, es, xs, ps]
  where ts = mkTypeEnvStr tv--show tv
        es = mkExprEnvStr ev
        xs = show expr
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
        mkExprStr' l@(Lam n e t) i = off i ++  "Lam (" ++ show n ++ "\n" ++ mkExprStr' e (i + 1) ++ " " ++ show t ++")"
        mkExprStr' a@(App e1 e2) i = off i ++ "App (\n" ++ mkExprStr' e1 (i + 1) ++ "\n" ++ mkExprStr' e2 (i + 1) ++ "\n" ++ off i ++ ")" 
        mkExprStr' c@(Case e1 ae t) i = off i ++ "Case (\n" ++ mkExprStr' e1 (i + 1) ++ "\n" ++ mkAltExprStr ae (i + 1) ++ " " ++ show t ++ ")"
        mkExprStr' x i = off i ++ show x


        mkAltExprStr :: [(Alt, Expr)] -> Int -> String
        mkAltExprStr [] i = ""
        mkAltExprStr ((a, e):xs) i = off i ++ "(" ++ show a ++ ",\n" ++ mkExprStr' e (i + 1) ++ ")" ++ mkAltExprStr xs i

        off :: Int -> String
        off i = duplicate "   " i


duplicate :: String -> Int -> String
duplicate s 0 = ""
duplicate s n = s ++ duplicate s (n - 1)