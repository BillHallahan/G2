{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DeBruijn.Interpreter ( Expr (..)
                            , Ident
                            , eval
                            , app
                            , num) where

import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = Int

data Expr = Lam Expr
          | Var Ident
          | App Expr Expr
          deriving (Show, Read, Eq, Data)

$(derivingG2Rep ''Expr)

type Stack = [Expr]

eval :: Expr -> Expr
eval = eval' []

eval' :: Stack -> Expr -> Expr
eval' stck (App ec ea) =
    let
        ea' = eval' stck ea
    in
    case eval' stck ec of
        Lam el -> eval' (ea':stck) el
        ec' -> App ec' ea'  
eval' stck (Var i) = stck !! (i - 1) 
eval' _ e = e

app :: [Expr] -> Expr
app = foldl1 App

num :: Int -> Expr
num n = Lam $ Lam $ app (replicate n (Var 2) ++ [Var 1])