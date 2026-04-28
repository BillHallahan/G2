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
import Sygus.ParseSygus (SmtCmd(DeclareDatatype))

type SMTNameBldr = Builder
type SMTName = String

-- | These define the kinds of top level calls we give to the SMT solver.
data SMTHeader = Assert !SMTAST
               | AssertSoft !SMTAST (Maybe T.Text)
               | Minimize !SMTAST
               | DefineFun SMTName [(SMTName, Sort)] Sort !SMTAST
               | DeclareFun SMTName [Sort] Sort
               | DeclareDatatypes [SMTDataType]
               | VarDecl SMTNameBldr Sort
               | SetLogic Logic
               | Comment String
               deriving (Show)

data SMTDataType = SmtDT { dt_name :: SMTName
                         , dt_tyvars :: [SMTName]
                         , dt_constructors :: [(SMTName, [(SMTName, Sort)])]}
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
           | QF_SLIA -- ^ Strings (with linear integer arithmetic for length)
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
            | StrAppendSMT [SMTAST] -- ^ String append
            | FromInt !SMTAST -- ^ Convert Ints to Strings
            | StrLenSMT !SMTAST
            | StrLtSMT !SMTAST !SMTAST
            | StrLeSMT !SMTAST !SMTAST
            | StrGtSMT !SMTAST !SMTAST
            | StrGeSMT !SMTAST !SMTAST
            | (:!!) !SMTAST !SMTAST -- ^ String index
            | StrSubstrSMT !SMTAST !SMTAST !SMTAST
            | StrIndexOfSMT !SMTAST !SMTAST !SMTAST
            | StrContainsSMT !SMTAST !SMTAST
            | StrReplaceSMT !SMTAST !SMTAST !SMTAST
            | StrReplaceAllSMT !SMTAST !SMTAST !SMTAST
            | StrReplaceReSMT !SMTAST !SMTAST !SMTAST
            | StrReplaceReAllSMT !SMTAST !SMTAST !SMTAST
            | StrPrefixOfSMT !SMTAST !SMTAST
            | StrSuffixOfSMT !SMTAST !SMTAST
            | StrReverseSMT !SMTAST

            | FoldLeftSMT SMTName Sort SMTName Sort !SMTAST !SMTAST !SMTAST

            | InReSMT !SMTAST !SMTAST
            | ToReSMT !SMTAST
            | ReNoneSMT
            | ReAllSMT
            | ReAllCharSMT
            | ReConcatSMT !SMTAST !SMTAST
            | ReUnionSMT !SMTAST !SMTAST
            | ReInterSMT !SMTAST !SMTAST
            | ReStarSMT !SMTAST
            | ReRangeSMT !SMTAST !SMTAST
            | ReCompSMT !SMTAST

            | SeqEmptySMT Sort
            | SeqUnitSMT !SMTAST

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
          | SortSeq Sort
          | SortBool
          | SortArray Sort Sort
          | SortFunc [Sort] Sort
          | ParSort SMTName
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
    children(x :^ y) = [x, y]

    children (AbsSMT x) = [x]
    children (SqrtSMT x) = [x]
    children (QuotSMT x y) = [x, y]
    children (Modulo x y) = [x, y]
    children (Neg x) = [x]

    children (BVAdd x y) = [x, y]
    children (BVNeg x) = [x]
    children (BVMult x y) = [x, y]
    children (Concat x y) = [x, y]
    children (ShiftL x y) = [x, y]
    children (ShiftR x y) = [x, y]


    children (FpSMT x y z) = [x, y, z]
    children (FpNegSMT x) = [x]
    children (FpAddSMT x y) = [x, y]
    children (FpSubSMT x y) = [x, y]
    children (FpMulSMT x y) = [x, y]
    children (FpDivSMT x y) = [x, y]

    children (FpLeqSMT x y) = [x, y]
    children (FpLtSMT x y) = [x, y]
    children (FpGeqSMT x y) = [x, y]
    children (FpGtSMT x y) = [x, y]
    children (FpEqSMT x y) = [x, y]

    children (FpIsZero x) = [x]
    children (FpIsNegative x) = [x]

    children (FpSqrtSMT x) = [x]
    children (TruncZeroSMT x) = [x]

    children (IsNormalSMT x) = [x]
    children (IsNaNSMT x) = [x]
    children (IsInfiniteSMT x) = [x]

    children (ArrayConst x _ _) = [x]
    children (ArrayStore x y z) = [x, y, z]
    children (ArraySelect x y) = [x, y]
    children (Func _ xs) = xs

    children (StrAppendSMT xs) = xs
    children (FromInt x) = [x]
    children (StrLenSMT x) = [x]
    children (StrLtSMT x y) = [x, y]
    children (StrLeSMT x y) = [x, y]
    children (StrGtSMT x y) = [x, y]
    children (StrGeSMT x y) = [x, y]
    children (x :!! y) = [x, y]
    children (StrSubstrSMT x y z) = [x, y, z]
    children (StrIndexOfSMT x y z) = [x, y, z]
    children (StrReplaceSMT x y z) = [x, y, z]
    children (StrPrefixOfSMT x y) = [x, y]
    children (StrSuffixOfSMT x y) = [x, y]

    children (FoldLeftSMT _ _ _ _ x y z) = [x, y, z]

    children (InReSMT x y) = [x, y]
    children (ToReSMT x) = [x]
    children ReNoneSMT = []
    children ReAllSMT = []
    children ReAllCharSMT = []
    children (ReConcatSMT x y) = [x, y]
    children (ReUnionSMT x y) = [x, y]
    children (ReInterSMT x y) = [x, y]
    children (ReStarSMT x) = [x]
    children (ReRangeSMT x y) = [x, y]
    children (ReCompSMT x) = [x]

    children (SeqEmptySMT _) = []
    children (SeqUnitSMT x) = [x]

    children (IteSMT x x' x'') = [x, x', x'']
    children (SLet (_, x) x') = [x, x']

    children (FromCode x) = [x]
    children (ToCode x) = [x]

    children (FloatToIntSMT x) = [x]
    children (DoubleToIntSMT x) = [x]
    children (IntToFPSMT _ _ x) = [x]
    children (FPToFPSMT _ _ x) = [x]
    children (IntToRealSMT x) = [x]
    children (IntToBVSMT _ x) = [x]
    children (BVToIntSMT _ x) = [x]
    children (BVToNatSMT x) = [x]
    children (RealToFloat x) = [x]
    children (RealToDouble x) = [x]

    children (Named x _) = [x]

    children (ForAll _ _ x) = [x]

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
    modifyChildren f (x :<=> y) = f x :<=> f y

    modifyChildren f (x :+ y) = f x :+ f y
    modifyChildren f (x :- y) = f x :- f y
    modifyChildren f (x :* y) = f x :* f y
    modifyChildren f (x :/ y) = f x :/ f y
    modifyChildren f (x :^ y) = f x :^ f y

    modifyChildren f (AbsSMT x) = AbsSMT (f x)
    modifyChildren f (SqrtSMT x) = SqrtSMT (f x)
    modifyChildren f (QuotSMT x y) = QuotSMT (f x) (f y)
    modifyChildren f (Modulo x y) = Modulo (f x) (f y)
    modifyChildren f (Neg x) = Neg (f x)

    modifyChildren f (BVAdd x y) = BVAdd (f x) (f y)
    modifyChildren f (BVNeg x) = BVNeg (f x)
    modifyChildren f (BVMult x y) = BVMult (f x) (f y)
    modifyChildren f (Concat x y) = Concat (f x) (f y)
    modifyChildren f (ShiftL x y) = ShiftL (f x) (f y)
    modifyChildren f (ShiftR x y) = ShiftR (f x) (f y)

    modifyChildren f (FpSMT x y z) = FpSMT (f x) (f y) (f z)
    modifyChildren f (FpNegSMT x) = FpNegSMT (f x)
    modifyChildren f (FpAddSMT x y) = FpAddSMT (f x) (f y)
    modifyChildren f (FpSubSMT x y) = FpSubSMT (f x) (f y)
    modifyChildren f (FpMulSMT x y) = FpMulSMT (f x) (f y)
    modifyChildren f (FpDivSMT x y) = FpDivSMT (f x) (f y)

    modifyChildren f (FpLeqSMT x y) = FpLeqSMT (f x) (f y)
    modifyChildren f (FpLtSMT x y) = FpLtSMT (f x) (f y)
    modifyChildren f (FpGeqSMT x y) = FpGeqSMT (f x) (f y)
    modifyChildren f (FpGtSMT x y) = FpGtSMT (f x) (f y)
    modifyChildren f (FpEqSMT x y) = FpEqSMT (f x) (f y)

    modifyChildren f (FpIsZero x) = FpIsZero (f x)
    modifyChildren f (FpIsNegative x) = FpIsNegative (f x)

    modifyChildren f (FpSqrtSMT x) = FpSqrtSMT (f x)
    modifyChildren f (TruncZeroSMT x) = TruncZeroSMT (f x)

    modifyChildren f (IsNormalSMT x) = IsNormalSMT (f x)
    modifyChildren f (IsNaNSMT x) = IsNaNSMT (f x)
    modifyChildren f (IsInfiniteSMT x) = IsInfiniteSMT (f x)

    modifyChildren f (ArrayConst x y z) = ArrayConst (f x) y z
    modifyChildren f (ArrayStore x y z) = ArrayStore (f x) (f y) (f z)
    modifyChildren f (ArraySelect x y) = ArraySelect (f x) (f y)
    modifyChildren f (Func n xs) = Func n (map f xs)

    modifyChildren f (StrAppendSMT xs) = StrAppendSMT (map f xs)
    modifyChildren f (FromInt x) = FromInt (f x)
    modifyChildren f (StrLenSMT x) = StrLenSMT (f x)
    modifyChildren f (StrLtSMT x y) = StrLtSMT (f x) (f y)
    modifyChildren f (StrLeSMT x y) = StrLeSMT (f x) (f y)
    modifyChildren f (StrGtSMT x y) = StrGtSMT (f x) (f y)
    modifyChildren f (StrGeSMT x y) = StrGeSMT (f x) (f y)
    modifyChildren f (x :!! y) = f x :!! f y
    modifyChildren f (StrSubstrSMT x y z) = StrSubstrSMT (f x) (f y) (f z)
    modifyChildren f (StrIndexOfSMT x y z) = StrIndexOfSMT (f x) (f y) (f z)
    modifyChildren f (StrContainsSMT x y) = StrContainsSMT (f x) (f y)
    modifyChildren f (StrReplaceSMT x y z) = StrReplaceSMT (f x) (f y) (f z)
    modifyChildren f (StrReplaceAllSMT x y z) = StrReplaceAllSMT (f x) (f y) (f z)
    modifyChildren f (StrReplaceReSMT x y z) = StrReplaceReSMT (f x) (f y) (f z)
    modifyChildren f (StrReplaceReAllSMT x y z) = StrReplaceReAllSMT (f x) (f y) (f z)
    modifyChildren f (StrPrefixOfSMT x y) = StrPrefixOfSMT (f x) (f y)
    modifyChildren f (StrSuffixOfSMT x y) = StrSuffixOfSMT (f x) (f y)
    
    modifyChildren f (FoldLeftSMT n1 s1 n2 s2 x y z) = FoldLeftSMT n1 s1 n2 s2 (f x) (f y) (f z)

    modifyChildren f (InReSMT x y) = InReSMT (f x) (f y)
    modifyChildren f (ToReSMT x) = ToReSMT (f x)
    modifyChildren _ ReNoneSMT = ReNoneSMT
    modifyChildren _ ReAllSMT = ReAllSMT
    modifyChildren _ ReAllCharSMT = ReAllCharSMT
    modifyChildren f (ReConcatSMT x y) = ReConcatSMT (f x) (f y)
    modifyChildren f (ReUnionSMT x y) = ReUnionSMT (f x) (f y)
    modifyChildren f (ReInterSMT x y) = ReInterSMT (f x) (f y)
    modifyChildren f (ReStarSMT x) = ReStarSMT (f x)
    modifyChildren f (ReRangeSMT x y) = ReRangeSMT (f x) (f y)
    modifyChildren f (ReCompSMT x) = ReCompSMT (f x)

    modifyChildren _ (SeqEmptySMT s) = SeqEmptySMT s
    modifyChildren f (SeqUnitSMT x) = SeqUnitSMT (f x)

    modifyChildren f (IteSMT x x' x'') = IteSMT (f x) (f x') (f x'')
    modifyChildren f (SLet (n, x) x') = SLet (n, f x) (f x')

    modifyChildren f (FromCode x) = FromCode (f x)
    modifyChildren f (ToCode x) = ToCode (f x)

    modifyChildren f (FloatToIntSMT x) = FloatToIntSMT (f x)
    modifyChildren f (DoubleToIntSMT x) = DoubleToIntSMT (f x)
    modifyChildren f (IntToFPSMT i1 i2 x) = IntToFPSMT i1 i2 (f x)
    modifyChildren f (FPToFPSMT i1 i2 x) = FPToFPSMT i1 i2 (f x)
    modifyChildren f (IntToRealSMT x) = IntToRealSMT (f x)
    modifyChildren f (IntToBVSMT i x) = IntToBVSMT i (f x)
    modifyChildren f (BVToIntSMT i x) = BVToIntSMT i (f x)
    modifyChildren f (BVToNatSMT x) = BVToNatSMT (f x)
    modifyChildren f (RealToFloat x) = RealToFloat (f x)
    modifyChildren f (RealToDouble x) = RealToDouble (f x)

    modifyChildren f (Named x n) = Named (f x) n

    modifyChildren f (ForAll n s x) = ForAll n s (f x)

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
