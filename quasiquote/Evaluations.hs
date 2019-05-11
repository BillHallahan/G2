{-# LANGUAGE QuasiQuotes #-}

module Evaluations where

import Data.Time.Clock
import G2.QuasiQuotes.QuasiQuotes

import Arithmetics.Interpreter as A
import NQueens.Encoding as Q
import DeBruijn.Interpreter as D
import RegEx.RegEx as R


timeIOAction :: IO a -> IO (a, NominalDiffTime)
timeIOAction action = do
  start <- getCurrentTime
  res <- action
  end <- getCurrentTime
  let diff = diffUTCTime end start
  return (res, diff)

timeIOActionPrint :: Show a => IO a -> IO ()
timeIOActionPrint action = do
  (res, time) <- timeIOAction action
  putStrLn $ show res
  putStrLn $ "time: " ++ show time


-------------------------------------------
-------------------------------------------
-- Section 2 (Arithmetics)
searchBadEnv :: Stmts -> IO (Maybe Env)
searchBadEnv =
  [g2| \(stmts :: Stmts) -> ?(env :: Env) |
        evalStmts env stmts == Nothing|]

envTest :: BExpr -> IO (Maybe Env)
envTest = [g2|\(b :: BExpr) -> ?(env :: Env) |
                evalB env b |]

badProg :: Stmts
badProg =
  [
    Assign "k" (I 1),
    Assign "i" (I 0),
    -- Assign "j" (I 0),
    Assign "n" (I 5),
    While (A.Or (Lt (A.Var "i") (A.Var "n"))
              (Eq (A.Var "i") (A.Var "n")))
          [ Assign "i" (Add (A.Var "i") (I 1))
          , Assign "j" (Add (A.Var "j") (A.Var "i"))
          ],
    Assign "z" (Add (A.Var "k") (Add (A.Var "i") (A.Var "j"))),
    Assert (Lt (Mul (A.Var "n") (I 2)) (A.Var "z"))
  ]

productSumTest :: BExpr
productSumTest =
  And
    ((Eq 
      (Mul (A.Var "x") (A.Var "y"))
      (Add (A.Var "x") (A.Var "y"))))
    (Lt (I 0) (A.Var "x"))

runArithmeticsEval :: IO ()
runArithmeticsEval = do
  putStrLn "------------------------"
  putStrLn "-- Arithmetics Eval -------"
  timeIOActionPrint $ searchBadEnv badProg
  timeIOActionPrint $ envTest productSumTest
  putStrLn ""



-------------------------------------------
-------------------------------------------
-- Section 5.1 (n Queens)


-------------------------------------------
-------------------------------------------
-- Section 5.2 (Lambda Calculus)

solveDeBruijn :: [([Expr], Expr)] -> IO (Maybe Expr)
solveDeBruijn =
    [g2| \(es :: [([Expr], Expr)]) -> ?(func :: Expr) |
         all (\e -> (eval (app (func:fst e))) == snd e) es |]

idDeBruijn :: [([D.Expr], D.Expr)]
idDeBruijn = [ ([num 1], num 1)
             , ([num 2], num 2) ]

const2Example :: [([D.Expr], D.Expr)]
const2Example =
  [ ([num 1, num 2], num 1)
  , ([num 2, num 3], num 2) ]                

trueLam :: D.Expr
trueLam = Lam (Lam (D.Var 2))

falseLam :: D.Expr
falseLam = Lam (Lam (D.Var 1))

orExample :: [([D.Expr], D.Expr)]
orExample =
  [ ([trueLam, trueLam], trueLam)
  , ([falseLam, falseLam], falseLam)
  , ([falseLam, trueLam], trueLam)
  , ([trueLam, falseLam], trueLam )]


runDeBruijnEval :: IO ()
runDeBruijnEval = do
  putStrLn "------------------------"
  putStrLn "-- DeBruijn Eval -------"
  timeIOActionPrint $ solveDeBruijn idDeBruijn
  timeIOActionPrint $ solveDeBruijn const2Example
  timeIOActionPrint $ solveDeBruijn orExample
  putStrLn ""


-------------------------------------------
-------------------------------------------
-- Section 5.3 (Regular Expressions)

stringSearch :: RegEx -> IO (Maybe String)
stringSearch =
  [g2| \(r :: RegEx) -> ?(str :: String) |
        match r str |]

-- (a + b)* c (d + (e f)*)
regexExample :: RegEx
regexExample =
  Concat (Star (R.Or (Atom 'a') (Atom 'b')))
         (Concat (Atom 'c')
                 (R.Or (Atom 'd')
                     (Concat (Atom 'e')
                             (Atom 'f'))))

runRegExEval :: IO ()
runRegExEval = do
  putStrLn "------------------------"
  putStrLn "-- RegEx Eval ----------"
  timeIOActionPrint $ stringSearch regexExample
  putStrLn ""



-------------------------------------------
-------------------------------------------


