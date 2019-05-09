{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DeBruijn.Interpreter ( Expr (..)
                            , Ident
                            , eval
                            , app
                            , num
                            , solveDeBruijn2) where

import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = Int

data Expr = Lam Expr
          | Var Ident
          | App Expr Expr
          deriving (Show, Read, Eq, Data)

$(derivingG2Rep ''Expr)

type LamStack = [Expr]
type AppStack = [Expr]

eval :: Expr -> Expr
eval = eval' [] []

eval' :: LamStack -> AppStack -> Expr -> Expr
eval' lamstck appstck (App ec ea) = eval' lamstck (ea:appstck) ec
eval' lamstck (ea:appstck) (Lam e) = eval' (ea:lamstck) appstck (App e ea)
eval' lamstck _ (Var i) = lamstck !! (i - 1) 
eval' _ _ e = e

app :: [Expr] -> Expr
app = foldl1 App

num :: Int -> Expr
num n = Lam $ Lam $ app (replicate n (Var 2) ++ [Var 1])

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
                                        (App (Var 1) (Var 3))
                                        (App (Var 2) (Var 1))
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
