{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Arithmetics.Interpreter where

import Control.Monad
import Data.Data
import G2.QuasiQuotes.G2Rep

type Ident = String
type Env = [(Ident, Int)]

data AExpr = I Int | Var Ident
    | Add AExpr AExpr | Mul AExpr AExpr
    deriving (Eq, Show, Data)

$(derivingG2Rep ''AExpr)

data BExpr = Not BExpr | And BExpr BExpr | Or BExpr BExpr
    | Lt AExpr AExpr | Eq AExpr AExpr
    deriving (Eq, Show, Data)

$(derivingG2Rep ''BExpr)

type Stmts = [Stmt]
data Stmt = Assign Ident AExpr
          | If BExpr Stmts Stmts
          | While BExpr Stmts
          | Assert BExpr
          deriving (Eq, Show, Data)
          
$(derivingG2Rep ''Stmt)

type Bound = [Ident]
type Return = Ident
data Func = Func Bound Stmts Return

$(derivingG2Rep ''Func)

evalFunc :: [Int] -> Func -> Maybe Int
evalFunc is (Func b s r) =
  lookup r =<< evalStmts (zip b is) s

evalStmts :: Env -> Stmts -> Maybe Env
evalStmts = foldM evalStmt  

evalStmt :: Env -> Stmt -> Maybe Env
evalStmt env (Assign ident aexpr) =
  Just $ (ident, evalA env aexpr):env
evalStmt env (If bexpr lhs rhs) =
  if evalB env bexpr
    then evalStmts env lhs
    else evalStmts env rhs
evalStmt env (While bexpr loop) =
  if evalB env bexpr
    then evalStmts env (loop ++ [While bexpr loop])
    else Just env
evalStmt env (Assert bexpr) =
  if evalB env bexpr
    then Just env
    else Nothing

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
evalB env (Or lhs rhs) =
  evalB env lhs || evalB env rhs
evalB env (Lt lhs rhs) =
  evalA env lhs < evalA env rhs
evalB env (Eq lhs rhs) =
  evalA env lhs == evalA env rhs

