{-# LANGUAGE QuasiQuotes #-}

module Arithmetics.Test where

import Arithmetics.Interpreter
import G2.QuasiQuotes.QuasiQuotes

productTest :: IO (Maybe (AExpr, AExpr))
productTest =
  [g2| \(a :: Int) -> ?(s1 :: AExpr)
                      ?(s2 :: AExpr) |
    let env = [("x", 23), ("y", 59)] in
    let lhs = Mul (Var "x") (Var "y") in
    let rhs = Mul s1 s2 in
      evalB env (Eq lhs rhs) |] 0

envTest :: BExpr -> IO (Maybe Env)
envTest = [g2|\(b :: BExpr) -> ?(env :: Env) |
                evalB env b |]

assertViolation :: Stmts -> IO (Maybe Env)
assertViolation = [g2|\(stmts :: Stmts) -> ?(env :: Env) |
                       evalStmts env stmts == Nothing|]

productSumTest :: IO (Maybe Env)
productSumTest =
    envTest $ And
                ((Eq 
                    (Mul (Var "x") (Var "y"))
                    (Add (Var "x") (Var "y"))))
                (Lt (I 0) (Var "x"))
{-
linearTest :: IO (Maybe (AExpr, AExpr))
linearTest =
  [g2| \(a :: Int) -> ?(s1 :: AExpr)
                      ?(s2 :: AExpr) |
    let env = [("w", 17), ("x", 19), ("y", 23), ("z" 29)] in
-}



