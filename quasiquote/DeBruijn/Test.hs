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