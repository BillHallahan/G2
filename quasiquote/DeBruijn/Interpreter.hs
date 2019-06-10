{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DeBruijn.Interpreter ( Expr (..)
                            , Ident
                            , eval
                            , app
                            , lams
                            , num) where

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