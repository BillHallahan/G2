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


productSumAssertTest :: IO (Maybe Env)
productSumAssertTest = assertViolation
    [ If (Lt (I 0) (Var "x"))
      [ Assert (Not
                 (Eq
                   (Mul (Var "x") (Var "y"))
                   (Add (Var "x") (Var "y"))
                 )
               )
      ]
      []
    ]

assertViolationTest1 :: IO (Maybe Env)
assertViolationTest1 = assertViolation
  [ Assert (Lt (I 5) (I 3)) ]

-- x^2 + y^2 + z^2 < (x + y + z)^2
assertViolationTest2 :: IO (Maybe Env)
assertViolationTest2 = assertViolation
  [ Assign "v1" (Add (Var "x") (Add (Var "y") (Var "z")))
  , Assign "v1" (Mul (Var "v1") (Var "v1"))
  , Assign "v2" (Add (Mul (Var "x") (Var "x"))
                  (Add (Mul (Var "y") (Var "y"))
                       (Mul (Var "z") (Var "z"))))
  , Assert (Lt (Var "v2") (Var "v1"))
  ]


assertViolationTest3 :: IO (Maybe Env)
assertViolationTest3 = assertViolation
  [
    Assign "k" (I 1),
    Assign "i" (I 0),
    Assign "j" (I 0),
    Assign "n" (I 5),
    While (Or (Lt (Var "i") (Var "n"))
              (Eq (Var "i") (Var "n")))
          [ Assign "i" (Add (Var "i") (I 1))
          , Assign "j" (Add (Var "j") (Var "i"))
          ],
    Assign "z" (Add (Var "k") (Add (Var "i") (Var "j"))),
    Assert (Lt (Mul (Var "n") (I 2)) (Var "z"))
  ]
  

assertViolationTest4 :: IO (Maybe Env)
assertViolationTest4 = assertViolation
  [
    Assign "k" (I 1),
    Assign "i" (I 0),
    -- Assign "j" (I 0),
    Assign "n" (I 5),
    While (Or (Lt (Var "i") (Var "n"))
              (Eq (Var "i") (Var "n")))
          [ Assign "i" (Add (Var "i") (I 1))
          , Assign "j" (Add (Var "j") (Var "i"))
          ],
    Assign "z" (Add (Var "k") (Add (Var "i") (Var "j"))),
    Assert (Lt (Mul (Var "n") (I 2)) (Var "z"))
  ]
 

