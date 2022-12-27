{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Simple.Simple1 ( Expr (..)
                            , eval
                            , num1) where

import Data.Data
import G2.QuasiQuotes.G2Rep

data Expr = Var Int
          | Lam Expr
          | App Expr Expr
          deriving (Show, Read, Eq, Data)

$(derivingG2Rep ''Expr)

type Stack = [Expr]


eval :: Stack -> Expr -> Expr
eval (e:stck) (Lam e') = eval stck (rep e e')
eval stck (App e1 e2) = eval (e2:stck) e1
eval stck e@(Var _) = foldl1 App (e:stck)

rep :: Expr -> Expr -> Expr
rep e (Var _) = e
rep e (Lam e') = Lam (rep e e')
rep e (App e1 e2) = App (rep e e1) (rep e e2)

num1 :: Expr
num1 = Lam (Var 1)