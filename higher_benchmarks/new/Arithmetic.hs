-- Adapted from:
-- G2Q: Haskell constraint solving
-- William T. Hallahan, Anton Xue, Ruzica Piskac

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Arithmetics.Interpreter where

import G2.Plugin

import Control.Monad
import Data.Data

type Ident = String
type Env = Ident -> Int

data AExpr = I Int | Var Ident
    | Add AExpr AExpr | Mul AExpr AExpr
    deriving (Eq, Show, Data)

data BExpr = Not BExpr | And BExpr BExpr | Or BExpr BExpr
    | Lt AExpr AExpr | Eq AExpr AExpr
    deriving (Eq, Show, Data)

type Stmts = [Stmt]
data Stmt = Assign Ident AExpr
          | If BExpr Stmts Stmts
          | While BExpr Stmts
          | Assert BExpr
          deriving (Eq, Show, Data)
          
type Bound = [Ident]
type Return = Ident
data Func = Func Bound Stmts Return

evalStmtsUnsafe :: Env -> Stmts -> Bool
evalStmtsUnsafe env stmts =
  case evalStmts env stmts of
      Just _ -> True
      Nothing -> error "Assertion violation"

evalStmts :: Env -> Stmts -> Maybe Env
evalStmts = foldM evalStmt  

evalStmt :: Env -> Stmt -> Maybe Env
evalStmt env (Assign ident aexpr) =
  Just $ \x -> case x == ident of
                    True  -> evalA env aexpr
                    False -> env x -- Just $ (ident, evalA env aexpr):env
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
evalA env (Var ident) = env ident

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

-- Test Programs

prog1 :: Stmts
prog1 =
  [
    Assign "k" (I 1),
    -- Assign "i" (I 0),
    -- Assign "j" (I 0),
    Assign "n" (I 5),
    While (Or (Lt (Var "i") (Var "n"))
              (Eq (Var "i") (Var "n")))
          [ Assign "i" (Add (Var "i") (I 1))
          , Assign "j" (Add (Var "j") (Var "i"))
          ],
    Assign "z" (Add (Var "k") (Add (Var "i") (Var "j"))),
    Assert (Lt (Mul (Var "n") (I 2)) (Var "z"))
  ]

{-# ANN evalProg1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --returns-true --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN evalProg1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --returns-true --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
evalProg1 :: Env -> Bool
evalProg1 env = evalStmtsUnsafe env prog1