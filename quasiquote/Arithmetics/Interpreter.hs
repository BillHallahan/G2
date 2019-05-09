{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Arithmetics.Interpreter where

import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = String
type Env = [(Ident, Int)]

data AExpr = I Int | Var Ident
    | Add AExpr AExpr | Mul AExpr AExpr
  deriving (Eq, Show, Data)

$(derivingG2Rep ''AExpr)

data BExpr = Not BExpr | And BExpr BExpr
    | Lt AExpr AExpr | Eq AExpr AExpr
  deriving (Eq, Show, Data)

$(derivingG2Rep ''BExpr)

evalA :: Env -> AExpr -> Int
evalA _ (I int) = int
evalA env (Add lhs rhs) =
  evalA env lhs + evalA env rhs
evalA env (Mul lhs rhs) =
  evalA env lhs * evalA env rhs
evalA env (Var ident) =
  case lookup ident env of
    Just int -> int
    _ -> error $
          "lookup with " ++ show (ident, env)

evalB :: Env -> BExpr -> Bool
evalB env (Not bexpr) = not $ evalB env bexpr
evalB env (And lhs rhs) =
  evalB env lhs && evalB env rhs
evalB env (Lt lhs rhs) =
  evalA env lhs < evalA env rhs
evalB env (Eq lhs rhs) =
  evalA env lhs == evalA env rhs


