{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Simple.Simple1 ( Expr (..)
                            , Ident
                            , eval
                            , num1) where

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
eval' stck e = foldl1 App $ e:stck

rep :: Int -> Expr -> Expr -> Expr
rep i e v@(Var j)
    | i == j = e
    | otherwise = v
rep i e (Lam e') = Lam (rep (i + 1) e e')
rep i e (App e1 e2) = App (rep i e e1) (rep i e e2)

num1 :: Expr
num1 = Lam (Var 1)