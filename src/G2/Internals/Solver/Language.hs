-- | Language
--   Provides a language definition designed to closely resemble the SMTLIB2 language.

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Solver.Language
    ( module G2.Internals.Solver.Language
    , module G2.Internals.Language.AST
    , SMTModel
    , Result (..)) where

import G2.Internals.Language.Support (ExprEnv, CurrExpr, Model)
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Language.AST
import G2.Internals.Solver.Solver

import qualified Data.Map as M

type SMTName = String

-- | SMTHeader
-- These define the two kinds of top level calls we give to the SMT solver.
-- An assertion says the given SMTAST is true
-- A sort decl declares a new sort.
data SMTHeader = Assert SMTAST
               | VarDecl SMTName Sort
               | SetLogic Logic
               deriving (Show, Eq)

data Logic = ALL | QF_LIA | QF_LRA | QF_NIA | QF_NRA | QF_LIRA | QF_NIRA deriving (Show, Eq)

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
            | (:<=>) SMTAST SMTAST

            | (:+) SMTAST SMTAST
            | (:-) SMTAST SMTAST -- Subtraction
            | (:*) SMTAST SMTAST
            | (:/) SMTAST SMTAST
            | SqrtSMT SMTAST
            | QuotSMT SMTAST SMTAST
            | Modulo SMTAST SMTAST
            | Neg SMTAST --Unary negation

            | Tester Name SMTAST

            | Ite SMTAST SMTAST SMTAST
            | SLet (SMTName, SMTAST) SMTAST

            | VInt Integer
            | VFloat Rational
            | VDouble Rational
            | VBool Bool

            | V SMTName Sort

            | ItoR SMTAST
            deriving (Show, Eq)

data Sort = SortInt
          | SortFloat
          | SortDouble
          | SortBool
          deriving (Show, Eq)

isSat :: Result -> Bool
isSat SAT = True
isSat _ = False

type SMTModel = M.Map SMTName SMTAST

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
    children (x :<=> y) = [x, y]

    children (x :+ y) = [x, y]
    children (x :- y) = [x, y]
    children (x :* y) = [x, y]
    children (x :/ y) = [x, y]
    children (Neg x) = [x]

    children (Ite x x' x'') = [x, x', x'']
    children (SLet (_, x) x') = [x, x']

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

    modifyChildren _ e = e

instance AST Sort where
    children _ = []

    modifyChildren _ s = s

instance ASTContainer SMTHeader SMTAST where
    containedASTs (Assert a) = [a]
    containedASTs _ = []

    modifyContainedASTs f (Assert a) = Assert (f a)
    modifyContainedASTs _ s = s

instance ASTContainer SMTAST Sort where
    containedASTs (V _ s) = [s]
    containedASTs x = eval containedASTs x

    modifyContainedASTs f (V n s) = V n (modify f s)
    modifyContainedASTs f x = modify (modifyContainedASTs f) x

