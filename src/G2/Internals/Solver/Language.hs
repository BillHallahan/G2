-- | Language
--   Provides a language definition designed to closely resemble the SMTLIB2 language.

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Internals.Solver.Language
    ( module G2.Internals.Solver.Language
    , module G2.Internals.Language.AST) where

import G2.Internals.Language.Support (ExprEnv, CurrExpr)
import qualified G2.Internals.Language.Support as Support (Model) 
import G2.Internals.Language.Syntax hiding (Assert)
import G2.Internals.Language.AST

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

data Result = SAT
            | UNSAT
            | Unknown String
            deriving (Show, Eq)

isSat :: Result -> Bool
isSat SAT = True
isSat _ = False

type Model = M.Map SMTName SMTAST
type ExprModel = Support.Model

-- This class is used to describe the specific output format required by various solvers
-- By defining these functions, we can automatically convert from the SMTHeader and SMTAST
-- datatypes, to a form understandable by the solver.
class SMTConverter con ast out io | con -> ast, con -> out, con -> io where
    empty :: con -> out
    merge :: con -> out -> out -> out

    checkSat :: con -> io -> out -> IO Result
    checkSatGetModel :: con -> io -> out -> [SMTHeader] -> [(SMTName, Sort)] -> IO (Result, Maybe Model)
    checkSatGetModelGetExpr :: con -> io -> out -> [SMTHeader] -> [(SMTName, Sort)] -> ExprEnv -> CurrExpr -> IO (Result, Maybe Model, Maybe Expr)

    assert :: con -> ast -> out
    varDecl :: con -> SMTName -> ast -> out
    setLogic :: con -> Logic -> out

    (.>=) :: con -> ast -> ast -> ast
    (.>) :: con -> ast -> ast -> ast
    (.=) :: con -> ast -> ast -> ast
    (./=) :: con -> ast -> ast -> ast
    (.<) :: con -> ast -> ast -> ast
    (.<=) :: con -> ast -> ast -> ast

    (.&&) :: con -> ast -> ast -> ast
    (.||) :: con -> ast -> ast -> ast
    (.!) :: con -> ast -> ast
    (.=>) :: con -> ast -> ast -> ast
    (.<=>) :: con -> ast -> ast -> ast

    (.+) :: con -> ast -> ast -> ast
    (.-) :: con -> ast -> ast -> ast
    (.*) :: con -> ast -> ast -> ast
    (./) :: con -> ast -> ast -> ast
    smtQuot :: con -> ast -> ast -> ast
    smtModulo :: con -> ast -> ast -> ast
    smtSqrt :: con -> ast -> ast
    neg :: con -> ast -> ast
    itor :: con -> ast -> ast

    ite :: con -> ast -> ast -> ast -> ast

    --values
    int :: con -> Integer -> ast
    float :: con -> Rational -> ast
    double :: con -> Rational -> ast
    bool :: con -> Bool -> ast
    cons :: con -> SMTName -> [ast] -> Sort -> ast
    var :: con -> SMTName -> ast -> ast

    --sorts
    sortInt :: con -> ast
    sortFloat :: con -> ast
    sortDouble :: con -> ast
    sortBool :: con -> ast

    varName :: con -> SMTName -> Sort -> ast

sortName :: SMTConverter con ast out io => con -> Sort -> ast
sortName con SortInt = sortInt con
sortName con SortFloat = sortFloat con
sortName con SortDouble = sortDouble con
sortName con SortBool = sortBool con

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
