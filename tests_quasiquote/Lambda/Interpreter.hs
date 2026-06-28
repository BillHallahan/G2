{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Lambda.Interpreter where

import Data.Data
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
eval env (Var id_) =
  case lookup id_ env of
    Just expr -> eval env expr
    Nothing -> Const (Fun id_)
eval env (App (Lam i body) arg) =
  eval ((i, arg) : env) body
eval _ expr = expr

