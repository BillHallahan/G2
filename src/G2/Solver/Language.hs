-- | Language
--   Provides a language definition designed to closely resemble the SMTLIB2 language.

{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, PatternSynonyms #-}

module G2.Solver.Language
    ( module G2.Solver.Language
    , module G2.Language.AST
    , Result (..)) where

import G2.Language.AST
import G2.Solver.Solver

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.Map as M
import Text.Builder
import qualified Data.Text as T

type SMTNameBldr = Builder
type SMTName = String

-- | These define the kinds of top level calls we give to the SMT solver.
data SMTHeader = Assert !SMTAST
               | AssertSoft !SMTAST (Maybe T.Text)
               | Minimize !SMTAST
               | DefineFun SMTName [(SMTName, Sort)] Sort !SMTAST
               | DeclareFun SMTName [Sort] Sort
               | VarDecl SMTNameBldr Sort
               | SetLogic Logic
               | Comment String
               deriving (Show)

-- | Various logics supported by (some) SMT solvers 
data Logic = ALL
           | QF_LIA
           | QF_LRA
           | QF_NIA
           | QF_NRA
           | QF_LIRA
           | QF_NIRA
           | QF_UFLIA
           | QF_S -- ^ Strings   
           deriving (Show, Eq)

-- | These correspond to first order logic, arithmetic operators, and variables, as supported by an SMT Solver
-- Its use should be confined to interactions with G2.SMT.* 
data SMTAST = (:>=) !SMTAST !SMTAST
            | (:>) !SMTAST !SMTAST
            | (:=) !SMTAST !SMTAST
            | (:/=) !SMTAST !SMTAST
            | (:<) !SMTAST !SMTAST
            | (:<=) !SMTAST !SMTAST

            | SmtAnd ![SMTAST]
            | SmtOr ![SMTAST]
            | (:!) !SMTAST
            | (:=>) !SMTAST !SMTAST
            | (:<=>) !SMTAST !SMTAST

            | (:+) !SMTAST !SMTAST
            | (:-) !SMTAST !SMTAST -- ^ Subtraction
            | (:*) !SMTAST !SMTAST
            | (:/) !SMTAST !SMTAST
            | (:^) !SMTAST !SMTAST

            | AbsSMT !SMTAST
            | SqrtSMT !SMTAST
            | QuotSMT !SMTAST !SMTAST
            | Modulo !SMTAST !SMTAST
            | Neg !SMTAST -- ^ Unary negation

            -- BitVectors
            | BVAdd !SMTAST !SMTAST
            | BVNeg !SMTAST
            | BVMult !SMTAST !SMTAST
            | Concat !SMTAST !SMTAST
            | ShiftL !SMTAST !SMTAST
            | ShiftR !SMTAST !SMTAST

            -- Floating Point
            | FpSMT !SMTAST !SMTAST !SMTAST -- ^ Sign, Exponent, Significand 
            | FpNegSMT !SMTAST
            | FpAddSMT !SMTAST !SMTAST
            | FpSubSMT !SMTAST !SMTAST
            | FpMulSMT !SMTAST !SMTAST
            | FpDivSMT !SMTAST !SMTAST

            | FpLeqSMT !SMTAST !SMTAST
            | FpLtSMT !SMTAST !SMTAST
            | FpGeqSMT !SMTAST !SMTAST
            | FpGtSMT !SMTAST !SMTAST
            | FpEqSMT !SMTAST !SMTAST

            | FpIsZero !SMTAST
            | FpIsNegative !SMTAST

            | FpSqrtSMT !SMTAST
            | TruncZeroSMT !SMTAST

            | IsNormalSMT !SMTAST
            | IsNaNSMT !SMTAST
            | IsInfiniteSMT !SMTAST

            -- Arrays
            | ArrayConst !SMTAST Sort Sort
            | ArrayStore !SMTAST !SMTAST !SMTAST
            | ArraySelect !SMTAST !SMTAST

            | Func SMTName ![SMTAST] -- ^ Interpreted function

            -- Strings
            | (:++) !SMTAST !SMTAST -- ^ String append
            | FromInt !SMTAST -- ^ Convert Ints to Strings
            | StrLenSMT !SMTAST
            | StrLtSMT !SMTAST !SMTAST
            | StrLeSMT !SMTAST !SMTAST
            | StrGtSMT !SMTAST !SMTAST
            | StrGeSMT !SMTAST !SMTAST
            | (:!!) !SMTAST !SMTAST -- ^ String index
            | StrSubstrSMT !SMTAST !SMTAST !SMTAST
            | StrIndexOfSMT !SMTAST !SMTAST !SMTAST
            | StrReplaceSMT !SMTAST !SMTAST !SMTAST
            | StrPrefixOfSMT !SMTAST !SMTAST
            | StrSuffixOfSMT !SMTAST !SMTAST

            | IteSMT !SMTAST !SMTAST !SMTAST
            | SLet (SMTName, SMTAST) !SMTAST

            | FromCode !SMTAST
            | ToCode !SMTAST

            | VInt Integer
            | VWord Word
            | VFloat Float
            | VDouble Double
            | VReal Rational
            | VBitVec [Int]
            | VChar Char
            | VString String
            | VBool Bool

            | V SMTName Sort

            | FloatToIntSMT !SMTAST -- ^ Float to Integer conversion
            | DoubleToIntSMT !SMTAST -- ^ Double to Integer conversion
            | IntToFPSMT !Int !Int !SMTAST -- ^ Integer to floating point (with the given exponent and significand) conversion
            | FPToFPSMT !Int !Int !SMTAST -- ^ Floating point to floating point conversion- exponent and significand of the target fp must be provided
            | IntToRealSMT !SMTAST -- ^ Integer to Real conversion
            | IntToBVSMT Int !SMTAST -- ^ Int to BitVector (of indicated width) conversion
            | BVToIntSMT Int !SMTAST -- ^ BitVector (of indicated width) to Int conversion
            | BVToNatSMT !SMTAST -- ^ BitVector to unsigned Int
            | RealToFloat !SMTAST -- ^ Real to Float
            | RealToDouble !SMTAST -- ^ Real to Double

            | Named !SMTAST SMTName -- ^ Name a piece of the SMTAST, allowing it to be returned in unsat cores

            | ForAll SMTName Sort !SMTAST
            deriving (Show, Eq)

-- | Every `SMTAST` has a `Sort`
data Sort = SortInt
          | SortWord
          | SortFP Int Int -- Floating point with the indicated exponent and significand.
          | SortReal
          | SortBV Int
          | SortChar
          | SortString
          | SortBool
          | SortArray Sort Sort
          | SortFunc [Sort] Sort
          deriving (Show, Eq, Ord, Generic)

pattern SortFloat :: Sort
pattern SortFloat = SortFP 8 24

pattern SortDouble :: Sort
pattern SortDouble = SortFP 11 53

instance Hashable Sort

(.=.) :: SMTAST -> SMTAST -> SMTAST
x .=. y
  | x == y = VBool True
  | otherwise = x := y

(./=.) :: SMTAST -> SMTAST -> SMTAST
x ./=. y = x :/= y

(.&&.) :: SMTAST -> SMTAST -> SMTAST
(VBool True) .&&. x = x
x .&&. (VBool True) = x
(VBool False) .&&. _ = VBool False
_ .&&. (VBool False) = VBool False
x .&&. y = SmtAnd [x, y]

(.||.) :: SMTAST -> SMTAST -> SMTAST
(VBool True) .||. _ = VBool True
_ .||. (VBool True) = VBool True
(VBool False) .||. x = x
x .||. (VBool False) = x
x .||. y = SmtOr [x, y]

mkSMTAnd :: [SMTAST] -> SMTAST
mkSMTAnd = SmtAnd

mkSMTOr :: [SMTAST] -> SMTAST
mkSMTOr = SmtOr

isSat :: Result m u um -> Bool
isSat (SAT _) = True
isSat _ = False

mkSMTEmptyArray :: Sort -> Sort -> SMTAST
mkSMTEmptyArray = ArrayConst (VBool False)

mkSMTUniversalArray :: Sort -> Sort -> SMTAST
mkSMTUniversalArray = ArrayConst (VBool True)

mkSMTUnion :: SMTAST -> SMTAST -> SMTAST
mkSMTUnion s1 s2 = Func "union" [s1, s2]

mkSMTIntersection :: SMTAST -> SMTAST -> SMTAST
mkSMTIntersection s1 s2 = Func "intersection" [s1, s2]

mkSMTSingleton :: SMTAST -> Sort -> Sort -> SMTAST
mkSMTSingleton mem srt srt2 =
    ArrayStore (ArrayConst (VBool False) srt srt2) mem (VBool True)

mkSMTIsSubsetOf :: SMTAST -> SMTAST -> SMTAST
mkSMTIsSubsetOf s1 s2 = Func "subset" [s1, s2]

type SMTModel = M.Map SMTName SMTAST
type UnsatCore = HS.HashSet SMTName

instance AST SMTAST where
    children (x :>= y) = [x, y]
    children (x :> y) = [x, y]
    children (x := y) = [x, y]
    children (x :/= y) = [x, y]
    children (x :< y) = [x, y]
    children (x :<= y) = [x, y]

    children (SmtAnd xs) = xs
    children (SmtOr xs) = xs
    children ((:!) x) = [x]
    children (x :=> y) = [x, y]
    children (x :<=> y) = [x, y]

    children (x :+ y) = [x, y]
    children (x :- y) = [x, y]
    children (x :* y) = [x, y]
    children (x :/ y) = [x, y]
    children (Neg x) = [x]

    children (IteSMT x x' x'') = [x, x', x'']
    children (SLet (_, x) x') = [x, x']

    children (FromCode x) = [x]
    children (ToCode x) = [x]

    children _ = []

    modifyChildren f (x :>= y) = f x :>= f y
    modifyChildren f (x :> y) = f x :> f y
    modifyChildren f (x := y) = f x := f y
    modifyChildren f (x :/= y) = f x :/= f y
    modifyChildren f (x :< y) = f x :< f y
    modifyChildren f (x :<= y) = f x :<= f y

    modifyChildren f (SmtAnd xs) = SmtAnd (map f xs)
    modifyChildren f (SmtOr xs) = SmtOr (map f xs)
    modifyChildren f ((:!) x) = (:!) (f x)
    modifyChildren f (x :=> y) = f x :=> f y

    modifyChildren f (x :+ y) = f x :+ f y
    modifyChildren f (x :- y) = f x :- f y
    modifyChildren f (x :* y) = f x :* f y
    modifyChildren f (x :/ y) = f x :/ f y
    modifyChildren f (Neg x) = Neg (f x)

    modifyChildren f (FromCode x) = FromCode (f x)
    modifyChildren f (ToCode x) = ToCode (f x)

    modifyChildren f (IteSMT x x' x'') = IteSMT (f x) (f x') (f x'')
    modifyChildren f (SLet (n, x) x') = SLet (n, f x) (f x')

    modifyChildren _ e = e

instance AST Sort where
    children _ = []

    modifyChildren _ s = s

--                | DefineFun SMTName [(SMTName, Sort)] Sort !SMTAST

instance ASTContainer SMTHeader SMTAST where
    containedASTs (Assert a) = [a]
    containedASTs (AssertSoft a _) = [a]
    containedASTs (Minimize a) = [a]
    containedASTs (DefineFun _ _ _ a) = [a]
    containedASTs _ = []

    modifyContainedASTs f (Assert a) = Assert (f a)
    modifyContainedASTs f (AssertSoft a lbl) = AssertSoft (f a) lbl
    modifyContainedASTs f (Minimize a) = Minimize (f a)
    modifyContainedASTs f (DefineFun n ars r a) = DefineFun n ars r (f a)
    modifyContainedASTs _ s = s

instance ASTContainer SMTAST Sort where
    containedASTs (V _ s) = [s]
    containedASTs x = eval containedASTs x

    modifyContainedASTs f (V n s) = V n (modify f s)
    modifyContainedASTs f x = modify (modifyContainedASTs f) x

sortOf :: SMTAST -> Sort
sortOf (VInt _) = SortInt
sortOf (VFloat _) = SortFloat
sortOf (VDouble _) = SortDouble
sortOf (VReal _) = SortReal
sortOf (VString _) = SortString
sortOf (VChar _) = SortChar 
sortOf (VBool _) = SortBool
sortOf _ = error "sortOf: Unhandled SMTAST"
