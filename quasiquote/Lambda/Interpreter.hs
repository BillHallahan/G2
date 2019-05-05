{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Interpreter where

import Data.Data
import Data.List
import G2.QuasiQuotes.QuasiQuotes
import G2.QuasiQuotes.G2Rep

type Id = String

data Prim = I Int | B Bool | Fun Id
  deriving (Show, Eq, Data)

$(derivingG2Rep ''Prim)

data Expr
  = Var Id
  | Lam Id Expr
  | App Expr Expr
  | Const Prim
  deriving (Show, Eq, Data)

$(derivingG2Rep ''Expr)

type Env = [(Id, Expr)]

eval :: Env -> Expr -> Expr
eval env (Var id) =
  case lookup id env of
    Just expr -> eval env expr
    Nothing -> Const (Fun id)
eval env (App (Lam id body) arg) =
  eval ((id, arg) : env) body
eval env expr = expr
