{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DeBruijn.Interpreter ( Expr (..)
                            , Ident
                            , eval
                            , app
                            , lams
                            , num
                            , k
                            , solveDeBruijn2) where

import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = Int

data Expr = Var Ident
          | Lam Expr
          | App Expr Expr
          deriving (Show, Read, Eq, Data)

$(derivingG2Rep ''Expr)

type Stack = [Expr]

eval :: Expr -> Expr
eval = eval' []

eval' :: Stack -> Expr -> Expr
eval' (e:stck) (Lam e') = eval' stck (rep 1 e e')
eval' stck (App e1 e2) = eval' (e2:stck) e1
eval' stck e = app $ e:stck

rep :: Int -> Expr -> Expr -> Expr
rep i e v@(Var j)
    | i == j = e
    | otherwise = v
rep i e (Lam e') = Lam (rep (i + 1) e e')
rep i e (App e1 e2) = App (rep i e e1) (rep i e e2)

app :: [Expr] -> Expr
app = foldl1 App

lams :: Int -> Expr -> Expr
lams n e = iterate Lam e !! n

num :: Int -> Expr
num n = Lam $ Lam $ foldr1 App (replicate n (Var 2) ++ [Var 1])

k :: Expr
k = Lam 
    (Lam
        (Lam
            (App
                (App
                    (Var 3)
                    (Var 1)
                )
                (App
                    (Var 2)
                    (Var 1)
                )
            )
        )
    )

test1 :: Bool
test1 = eval (App (Lam (Var 1)) (num 4)) == num 4

test2 :: Bool
test2 = eval (App (App (Lam (Lam (Var 2))) (num 4)) (num 6)) == num 4

test3 :: Bool
test3 = eval (App 
                (App 
                    (App 
                        (Lam 
                            (Lam 
                                (Lam 
                                    (App
                                        (App (Var 1) (Var 2))
                                        (App (Var 2) (Var 3))
                                    )
                                )
                            )
                        )
                        (num 7)
                    )
                    (Lam (Var 1))
                )
                (Lam (Var 1))
            )
        == (num 7)

solveDeBruijn2 :: Expr -> [([Expr], Expr)] -> Bool
solveDeBruijn2 func = all (\e -> (eval (app (func:fst e))) == snd e)
