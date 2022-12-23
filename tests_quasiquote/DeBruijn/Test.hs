{-# LANGUAGE QuasiQuotes #-}

module DeBruijn.Test where

import DeBruijn.Interpreter
import G2.QuasiQuotes.QuasiQuotes

import RegEx.RegEx as R

solveDeBruijn :: [([Expr], Expr)] -> IO (Maybe Expr)
solveDeBruijn =
    [g2| \(es :: [([Expr], Expr)]) -> ?(func :: Expr) |
         all (\e -> (eval (app (func:fst e))) == snd e) es |]

appFunc :: [([Expr], Expr)] -> Expr -> Bool
appFunc es func = all (\e -> (eval (app (func:fst e))) == snd e) es

idDeBruijn :: [([Expr], Expr)]
idDeBruijn = [ ([num 1], num 1)
             , ([num 2], num 2) ]

const2Example :: [([Expr], Expr)]
const2Example =
  [ ([num 1, num 2], num 1)
  , ([num 2, num 3], num 2) ]                

trueLam :: Expr
trueLam = Lam (Lam (Var 2))

falseLam :: Expr
falseLam = Lam (Lam (Var 1))

notExample :: [([Expr], Expr)]
notExample =
  [ ([trueLam], falseLam)
  , ([falseLam], trueLam) ]

orExample :: [([Expr], Expr)]
orExample =
  [ ([trueLam, trueLam], trueLam)
  , ([falseLam, falseLam], falseLam)
  , ([falseLam, trueLam], trueLam)
  , ([trueLam, falseLam], trueLam )]

andExample :: [([Expr], Expr)]
andExample =
  [ ([trueLam, trueLam], trueLam)
  , ([falseLam, falseLam], falseLam)
  , ([falseLam, trueLam], falseLam)
  , ([trueLam, falseLam], falseLam )]


-- runDeBruijnEval :: IO ()
-- runDeBruijnEval = do
--   putStrLn "------------------------"
--   putStrLn "-- DeBruijn Eval -------"
--   timeIOActionPrint $ solveDeBruijn idDeBruijn
--   timeIOActionPrint $ solveDeBruijn const2Example
--   -- timeIOActionPrint $ solveDeBruijn notExample
--   timeIOActionPrint $ solveDeBruijn orExample
--   -- timeIOActionPrint $ solveDeBruijn andExample
--   putStrLn ""
