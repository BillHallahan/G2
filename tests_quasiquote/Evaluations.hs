{-# LANGUAGE QuasiQuotes #-}

module Evaluations where

import G2.QuasiQuotes.QuasiQuotes

import DeBruijn.Interpreter as D
import RegEx.RegEx as R


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

notExample :: [([D.Expr], D.Expr)]
notExample =
  [ ([trueLam], falseLam)
  , ([falseLam], trueLam) ]

orExample :: [([D.Expr], D.Expr)]
orExample =
  [ ([trueLam, trueLam], trueLam)
  , ([falseLam, falseLam], falseLam)
  , ([falseLam, trueLam], trueLam)
  , ([trueLam, falseLam], trueLam )]

andExample :: [([D.Expr], D.Expr)]
andExample =
  [ ([trueLam, trueLam], trueLam)
  , ([falseLam, falseLam], falseLam)
  , ([falseLam, trueLam], falseLam)
  , ([trueLam, falseLam], falseLam )]




-------------------------------------------
-------------------------------------------


