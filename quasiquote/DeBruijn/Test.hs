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
solveDeBruijnK = solveDeBruijn [ ([num 1, num 2], num 2)
                               , ([num 2, num 3], num 3)]

trueLam :: Expr
trueLam = Lam (Lam (Var 2))

falseLam :: Expr
falseLam = Lam (Lam (Var 1))

solveDeBruijnAnd :: IO (Maybe Expr)
solveDeBruijnAnd = solveDeBruijn [ ([trueLam, trueLam], trueLam)
                                 , ([falseLam, falseLam], falseLam)
                                 , ([falseLam, trueLam], falseLam) 
                                 , ([trueLam, falseLam], falseLam) ]

solveDeBruijnOr :: IO (Maybe Expr)
solveDeBruijnOr = solveDeBruijn [ ([trueLam, trueLam], trueLam)
                                  , ([falseLam, falseLam], falseLam)
                                  , ([falseLam, trueLam], trueLam) 
                                  , ([trueLam, falseLam], trueLam) ]

solveDeBruijnIte :: IO (Maybe Expr)
solveDeBruijnIte = solveDeBruijn [ ([trueLam, Var 2, Var 4], Var 2)
                                 , ([falseLam, Var 2, Var 4], Var 4) ]

solveDeBruijnS :: IO (Maybe Expr)
solveDeBruijnS =
    let
        k = Lam (Lam (Var 2))
    in
    solveDeBruijn
        [ ([Lam (Lam (Var 1)), Lam (Var 1), num 2], num 2)
        , ([Lam (Lam (Var 1)), Lam (Lam (Var 2)), num 3], num 3) ]
    -- [g2| \(_ :: ()) -> ?(func :: Expr) |
    --     let
    --         k = Lam (Lam (Var 2))
    --     in
    --     eval (App func (App k (App (num 1) (num 2)))) == num 2
    -- |] ()
    -- , ([Lam (Lam (Var 1)), Lam (num 3), num 1], num 3)]
    -- , ([Lam (Lam (Lam (Var 2))), Lam (Lam (Var 1)), num 1], Lam (Lam (num 1)))]
