{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DeBruijn.Interpreter ( Expr (..)
                            , Ident
                            , eval) where

import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = Int

data Expr = Lam Expr
          | Var Ident
          | App Expr Expr
          | Const Int
          deriving (Show, Read, Eq, Data)

$(derivingG2Rep ''Expr)

type Stack = [Expr]

eval :: Expr -> Expr
eval = eval' []

eval' :: Stack -> Expr -> Expr
eval' stck (App (Lam el) ea) = eval' (ea:stck) el
eval' stck (Var i) =  eval' stck $ stck !! (i - 1) 
eval' _ e = e