-- | Language
--   Provides a language definition designed to closely resemble the SMTLIB2 language.

{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.SMT.Language
    ( module G2.Internals.SMT.Language
    , module G2.Internals.Language.AST) where

import G2.Internals.Language.Support (ExprEnv, CurrExpr)
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Language.AST

import qualified Data.Map as M

type SMTName = String

-- | SMTHeader
-- These define the two kinds of top level calls we give to the SMT solver.
-- An assertion says the given SMTAST is true
-- A sort decl declares a new sort.
data SMTHeader = Assert SMTAST
               | SortDecl [(SMTName, [SMTName], [DC])]
               | VarDecl SMTName Sort
               deriving (Show, Eq)

-- | SMTAST
-- These coorespond to first order logic, arithmetic operators, and variables, as supported by an SMT Solver
-- Its use should be confined to interactions with G2.Internals.SMT.* 
data SMTAST = (:>=) SMTAST SMTAST
            | (:>) SMTAST SMTAST
            | (:=) SMTAST SMTAST
            | (:/=) SMTAST SMTAST
            | (:<) SMTAST SMTAST
            | (:<=) SMTAST SMTAST

            | (:&&) SMTAST SMTAST
            | (:||) SMTAST SMTAST
            | (:!) SMTAST
            | (:=>) SMTAST SMTAST

            | (:+) SMTAST SMTAST
            | (:-) SMTAST SMTAST -- Subtraction
            | (:*) SMTAST SMTAST
            | (:/) SMTAST SMTAST
            | Neg SMTAST --Unary negation

            | Tester Name SMTAST

            | Ite SMTAST SMTAST SMTAST
            | SLet (SMTName, SMTAST) SMTAST

            | VInt Int
            | VFloat Rational
            | VDouble Rational
            | VBool Bool
            | Cons SMTName [SMTAST] Sort

            | V SMTName Sort
            deriving (Show, Eq)

data Sort = SortInt
          | SortFloat
          | SortDouble
          | SortBool
          | Sort SMTName [Sort]
          deriving (Show, Eq)

data DC = DC SMTName [Sort] deriving (Show, Eq)

data Result = SAT
            | UNSAT
            | Unknown String
            deriving (Show, Eq)

isSat :: Result -> Bool
isSat SAT = True
isSat _ = False

type Model = M.Map SMTName SMTAST
type ExprModel = M.Map Name Expr

-- This data type is used to describe the specific output format required by various solvers
-- By defining these functions, we can automatically convert from the SMTHeader and SMTAST
-- datatypes, to a form understandable by the solver.
data SMTConverter ast out io =
    SMTConverter {
          empty :: out
        , merge :: out -> out -> out

        , checkSat :: io -> out -> IO Result
        , checkSatGetModelGetExpr :: io -> out -> [SMTHeader] -> [(SMTName, Sort)] -> ExprEnv -> CurrExpr -> IO (Result, Maybe Model, Maybe Expr)

        , assert :: ast -> out
        , sortDecl :: [(SMTName, [SMTName], [DC])] -> out
        , varDecl :: SMTName -> ast -> out

        , (.>=) :: ast -> ast -> ast
        , (.>) :: ast -> ast -> ast
        , (.=) :: ast -> ast -> ast
        , (./=) :: ast -> ast -> ast
        , (.<) :: ast -> ast -> ast
        , (.<=) :: ast -> ast -> ast

        , (.&&) :: ast -> ast -> ast
        , (.||) :: ast -> ast -> ast
        , (.!) :: ast -> ast
        , (.=>) :: ast -> ast -> ast

        , (.+) :: ast -> ast -> ast
        , (.-) :: ast -> ast -> ast
        , (.*) :: ast -> ast -> ast
        , (./) :: ast -> ast -> ast
        , neg :: ast -> ast

        , tester :: SMTName -> ast -> ast

        , ite :: ast -> ast -> ast -> ast

        --values
        , int :: Int -> ast
        , float :: Rational -> ast
        , double :: Rational -> ast
        , bool :: Bool -> ast
        , cons :: SMTName -> [ast] -> Sort -> ast
        , var :: SMTName -> ast -> ast

        --sorts
        , sortInt :: ast
        , sortFloat :: ast
        , sortDouble :: ast
        , sortBool :: ast
        , sortADT :: SMTName -> [Sort] -> ast

        , varName :: SMTName -> Sort -> ast
    }

sortName :: SMTConverter ast out io -> Sort -> ast
sortName con SortInt = sortInt con
sortName con SortFloat = sortFloat con
sortName con SortDouble = sortDouble con
sortName con SortBool = sortBool con
sortName con (Sort n s) = sortADT con n s

instance AST SMTAST where
    children (x :>= y) = [x, y]
    children (x :> y) = [x, y]
    children (x := y) = [x, y]
    children (x :/= y) = [x, y]
    children (x :< y) = [x, y]
    children (x :<= y) = [x, y]

    children (x :&& y) = [x, y]
    children (x :|| y) = [x, y]
    children ((:!) x) = [x]
    children (x :=> y) = [x, y]

    children (x :+ y) = [x, y]
    children (x :- y) = [x, y]
    children (x :* y) = [x, y]
    children (x :/ y) = [x, y]
    children (Neg x) = [x]

    children (Ite x x' x'') = [x, x', x'']
    children (SLet (_, x) x') = [x, x']

    children (Cons _ x _) = x

    children _ = []

    modifyChildren f (x :>= y) = f x :>= f y
    modifyChildren f (x :> y) = f x :> f y
    modifyChildren f (x := y) = f x := f y
    modifyChildren f (x :/= y) = f x :/= f y
    modifyChildren f (x :< y) = f x :< f y
    modifyChildren f (x :<= y) = f x :<= f y

    modifyChildren f (x :&& y) = f x :&& f y
    modifyChildren f (x :|| y) = f x :|| f y
    modifyChildren f ((:!) x) = (:!) (f x)
    modifyChildren f (x :=> y) = f x :=> f y

    modifyChildren f (x :+ y) = f x :+ f y
    modifyChildren f (x :- y) = f x :- f y
    modifyChildren f (x :* y) = f x :* f y
    modifyChildren f (x :/ y) = f x :/ f y
    modifyChildren f (Neg x) = Neg (f x)

    modifyChildren f (Ite x x' x'') = Ite (f x) (f x') (f x'')
    modifyChildren f (SLet (n, x) x') = SLet (n, f x) (f x')

    modifyChildren f (Cons n x s) = Cons n (map f x) s

    modifyChildren _ e = e

instance AST Sort where
    children (Sort _ s) = s
    children _ = []

    modifyChildren f (Sort n s) = Sort n (map f s) 
    modifyChildren _ s = s

instance ASTContainer SMTHeader SMTAST where
    containedASTs (Assert a) = [a]
    containedASTs _ = []

    modifyContainedASTs f (Assert a) = Assert (f a)
    modifyContainedASTs _ s = s

instance ASTContainer SMTAST Sort where
    containedASTs (Cons _ _ s) = [s]
    containedASTs (V _ s) = [s]
    containedASTs x = eval containedASTs x

    modifyContainedASTs f (Cons n x s) = Cons n x (modify f s)
    modifyContainedASTs f (V n s) = V n (modify f s)
    modifyContainedASTs f x = modify (modifyContainedASTs f) x
