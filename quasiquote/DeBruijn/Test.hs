{-# LANGUAGE QuasiQuotes #-}

module DeBruijn.Test where

import DeBruijn.Interpreter
import G2.QuasiQuotes.QuasiQuotes

solveDeBruijn1 :: IO (Maybe Expr)
solveDeBruijn1 =
    [g2| \(x :: Int) -> ?(syExpr :: Expr) |
        let expr = App syExpr in
          eval (expr (Lam (Var 1))) == (Lam (Var 1))
        && eval (expr (Lam (Var 2))) == (Lam (Var 2)) |] 6

solveDeBruijn :: [([Expr], Expr)] -> IO (Maybe Expr)
solveDeBruijn =
    [g2| \(es :: [([Expr], Expr)]) -> ?(func :: Expr) |
         all (\e -> (eval (app (func:fst e))) == snd e) es |]

solveDeBruijnI :: IO (Maybe Expr)
solveDeBruijnI = solveDeBruijn [ ([num 1], num 1)
                               , ([num 2], num 2) ]

solveDeBruijnK :: IO (Maybe Expr)
solveDeBruijnK = solveDeBruijn [ ([num 1, num 2], num 1)
                               , ([num 2, num 3], num 2)]