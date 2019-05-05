{-# LANGUAGE QuasiQuotes #-}

module Lambda.Lambda where

import Lambda.Interpreter
import G2.QuasiQuotes.QuasiQuotes

lambdaTest1 :: IO (Maybe Expr)
lambdaTest1 = [g2| \(x :: Int ) -> ?(symExpr :: Expr) |
      let env = [] in
      let expr = App (Lam "b" (Var "b")) symExpr in
        eval env expr == (Const (I 40)) |] 0


lambdaTest2 :: IO (Maybe Expr)
lambdaTest2 = [g2| \(x :: Int ) -> ?(symExpr :: Expr) |
      let env = [] in
      let expr = symExpr in
        eval env expr == (Const (I 43)) |] 0
