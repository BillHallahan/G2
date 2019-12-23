-- | Language
--   Provides a language definition designed to closely resemble the SMTLIB2 language.

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Solver.Language
    ( module G2.Solver.Language
    , module G2.Language.AST
    , Result (..)) where

import G2.Language.AST
import G2.Solver.Solver

import qualified Data.Map as M
import Text.Builder

type SMTNameBldr = Builder
type SMTName = String

-- | These define the two kinds of top level calls we give to the SMT solver.
-- An assertion says the given SMTAST is true
-- A sort decl declares a new sort.
data SMTHeader = Assert SMTAST
               | VarDecl SMTNameBldr Sort
               | SetLogic Logic
               deriving (Show)

-- | Various logics supported by (some) SMT solvers 
data Logic = ALL | QF_LIA | QF_LRA | QF_NIA | QF_NRA | QF_LIRA | QF_NIRA deriving (Show, Eq)

-- | These correspond to first order logic, arithmetic operators, and variables, as supported by an SMT Solver
-- Its use should be confined to interactions with G2.SMT.* 
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
            | (:-) SMTAST SMTAST -- ^ Subtraction
            | (:*) SMTAST SMTAST
            | (:/) SMTAST SMTAST
            | SqrtSMT SMTAST
            | QuotSMT SMTAST SMTAST
            | Modulo SMTAST SMTAST
            | Neg SMTAST -- ^ Unary negation

            | StrLen SMTAST

            | Ite SMTAST SMTAST SMTAST
            | SLet (SMTNameBldr, SMTAST) SMTAST

            | VInt Integer
            | VFloat Rational
            | VDouble Rational
            | VChar Char
            | VBool Bool

            | V SMTNameBldr Sort

            | ItoR SMTAST -- ^ Integer to real conversion
            deriving (Show)

-- | Every `SMTAST` has a `Sort`
data Sort = SortInt
          | SortFloat
          | SortDouble
          | SortChar
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

