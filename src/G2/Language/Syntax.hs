{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Defines most of the central language in G2. This language closely resembles Core Haskell.
-- The central datatypes are `Expr` and t`Type`.

module G2.Language.Syntax
    ( module G2.Language.Syntax
    ) where

import GHC.Generics (Generic)
import Data.Bits
import Data.Data
import Data.Foldable
import Data.Hashable
import qualified Data.Text as T

-- | Binds `Id`s to `Expr`s, primarily in @let@ `Expr`s
type Binds = [(Id, Expr)]

-- | Records a location in the source code
data Loc = Loc { line :: Int
               , col :: Int
               , file :: String } deriving (Show, Eq, Read, Ord, Generic, Typeable, Data)

instance Hashable Loc

-- | Records a span in the source code.
--
-- Invariant:
--
-- >  file start == file end
data Span = Span { start :: Loc
                 , end :: Loc } deriving (Show, Eq, Read, Ord, Generic, Typeable, Data)

instance Hashable Span

-- | A name has three pieces: an occurence name, Maybe a module name, and a Unique Id.
data Name = Name T.Text (Maybe T.Text) Int (Maybe Span)
            deriving (Show, Read, Generic, Typeable, Data)

-- | Disregards the Span
instance Eq Name where
    Name n m i _ == Name n' m' i' _ = n == n' && m == m' && i == i'

-- | Disregards the Span
instance Ord Name where
    Name n m i _ `compare` Name n' m' i' _ = (n, m, i) `compare` (n', m', i')

-- | Disregards the Span
instance Hashable Name where
    hashWithSalt s (Name n m i _) =
        s `hashWithSalt`
        n `hashWithSalt`
        m `hashWithSalt` i

-- | Pairing of a `Name` with a t`Type`
data Id = Id Name Type deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

instance Hashable Id

-- | Indicates the purpose of the a Lambda binding
data LamUse = TermL -- ^ Binds at the term level 
            | TypeL -- ^ Binds at the type level
            deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable LamUse

-- | Extract the `Name` from an `Id`.
idName :: Id -> Name
idName (Id name _) = name

-- | The `sym_gens` field of a `State` is used to record the values generated by certain `SymGen`s.
-- This allows us to track, and eventually print to display to the user, values generated by (certain) `SymGen`s.
-- `SymGen`s tagged with `SLog` are logged, i.e. will be recorded in the `sym_gens` field. Those tagged by `SNoLog` are not logged.
data SymLog = SLog | SNoLog
    deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable SymLog

-- | Expressions, representing G2's intermediate language.
data Expr =
          -- | @`Var` `Id`@ is a variable.  Variables may be bound by a `Lam`, `Let`
          -- or `Case` `Expr`, or be bound in the `G2.Language.ExprEnv.ExprEnv`.  A variable may also be
          -- free (unbound), in which case it is symbolic
            Var Id
          -- | @v`Lit` t`Lit`@ denotes a literal.
          | Lit Lit
          -- | Primitive functions.  Should be wrapped in `App`s.
          | Prim Primitive Type
          -- | @v`Data` `DataCon`@ denotes a Data Constructor
          | Data DataCon
          {-| @`App` `Expr` `Expr`@ denotes function application.
            For example, the function call:

            @ f x y @
            would be represented as

            @ `App`
            (`App`
                (`Var` (`Id` (`Name` "f" Nothing 0 Nothing) (`TyFun` t (`TyFun` t t))))
                (`Var` (`Id` (`Name` "x" Nothing 0 Nothing) t))
            )
            (`Var` (`Id` (`Name` "y" Nothing 0 Nothing) t)) @
          -}
          | App Expr Expr
          -- | @`Lam` `LamUse` `Id` `Expr`@ denotes a lambda function.
          -- The `Id` is bound in the `Expr`.
          -- This binding may be on the type or term level, depending on the `LamUse`.
          | Lam LamUse Id Expr
          -- | @`Let` b e@ gives a mapping of `Name`s to `Expr`s in `b`, allowing those names
          -- to be used in `e`.
          | Let Binds Expr
          -- | @`Case` e i as@ splits into multiple `Alt`s (Alternatives),
          -- Depending on the value of @e@.  In each Alt, the `Id` @i@ is bound to @e@.
          -- The `Alt`s must always be exhaustive- there should never be a case where no `Alt`
          -- can match a given `Expr`.
          | Case Expr -- ^ Scrutinee
                 Id -- ^ Bindee
                 Type -- ^ Type of the case expression
                 [Alt] -- ^ Alternatives
                 
          -- | @v`Type` t`Type`@ gives a `Expr` level representation of a t`Type`.
          -- These only ever appear as the arguments to polymorphic functions,
          -- to determine the t`Type` bound to type level variables.
          | Type Type
          -- | @`Cast` e (t1 `:~` t2)@ casts @e@ from the t`Type` @t1@ to @t2@
          -- This requires that @t1@ and @t2@ have the same representation.
          | Cast Expr Coercion
          -- | @v`Coercion` t`Coercion`@ allows runtime passing of t`Coercion`s to `Cast`s.
          | Coercion Coercion
          -- | @`Tick` `Tickish` `Expr`@ records some extra information into an `Expr`.
          | Tick Tickish Expr
          -- | @`NonDet` [`Expr`]@ gives a nondeterministic choice between multiple options
          -- to continue execution with.
          | NonDet [Expr]
          -- | @`SymGen` t`Type`@ evaluates to a fresh symbolic variable of the given type.
          -- The `SymLog` determines whether the SymGen logs its generated value in the `State`s `sym_gens` field.
          | SymGen SymLog Type
          -- | @`Assume` b e@ takes a boolean typed expression @b@,  and an expression of
          -- arbitrary type @e@. During exectuion, @b@ is reduced to SWHNF, and assumed.
          -- Then, execution continues with @b@.
          | Assume (Maybe FuncCall) Expr Expr
          -- | @`Assert` fc b e@ is similar to `Assume`, but asserts the @b@ holds.
          -- The `Maybe` `FuncCall` allows us to optionally indicate that the
          -- assertion is related to a specific function.
          | Assert (Maybe FuncCall) Expr Expr
          deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Expr

-- | These are known, and G2-augmented operations, over unwrapped
-- data types such as Int#, Char#, Double#, etc.
-- Generally, calls to these should actually be created using the functions in:
--
--    "G2.Language.Primitives"
--
-- And evaluation over literals can be peformed with the functions in:
--
--     "G2.Execution.PrimitiveEval" 
data Primitive = -- Mathematical and logical operators
                 Ge
               | Gt
               | Eq
               | Neq
               | Lt
               | Le
               | And
               | Or
               | Not
               | Implies
               | Iff
               | Ite -- ^ Bool -> a -> a -> a, if-then-else, convertable to an SMT representation.  All arguments should be representable in the SMT solver.
               | Plus
               | Minus
               | Mult
               | Div
               | DivInt
               | Quot
               | Mod
               | Rem
               | Negate
               | Abs


               -- Rational
               | Sqrt
               | Exp

               -- BitVectors
               | AddBV
               | MinusBV
               | MultBV
               | ConcatBV
               | ShiftLBV
               | ShiftRBV

               -- Floating point operations
               | Fp -- ^ A floating point number, should be wrapped in arguments representing (Sign Exponent Significand).
                    -- Currently only supports being used in PathCons to be converted to SMT.
               | DecodeFloat
               | EncodeFloat

               | FpNeg
               | FpAdd
               | FpSub
               | FpMul
               | FpDiv

               | FpLeq
               | FpLt
               | FpGeq
               | FpGt
               | FpEq
               | FpNeq

               | FpSqrt

               | IsDenormalized
               | FpIsNegativeZero
               | IsNaN
               | IsInfinite

               | TruncZero
               | DecimalPart

               -- GHC conversions from data constructors to Int#, and vice versa
               | DataToTag
               | TagToEnum

               -- Numeric conversion
               | IntToFloat
               | IntToDouble
               | IntToRational
               | RationalToFloat
               | RationalToDouble
               | ToInteger
               | ToInt
               | BVToInt Int -- ^ Signed conversion, takes the width of the bit vector
               | BVToNat -- ^ Unsigned conversion
               
               -- String Handling
               | StrGt
               | StrGe
               | StrLt
               | StrLe
               | StrLen
               | StrAppend
               | Chr
               | OrdChar
               | WGenCat

               -- IO Handles
               | Handle Name -- ^ An IO Handle, the `Name` corresponds to a `HandleInfo` via a `State`s `handles` field
               | HandleGetPos -- ^ Handle -> String
               | HandleSetPos -- ^ String -> Handle -> ()
               | HandlePutChar -- ^ Char -> Handle -> ()

               -- Convert a positive Int to a String. (This matches the SMT Str.from_int function, which supports only positive Ints.)
               | IntToString
               
               -- MutVar#
               | MutVar Name
               | NewMutVar -- ^ `forall a d. a -> State# d -> MutVar# d a`.
               | ReadMutVar -- ^ `forall d a. MutVar# d a -> State# d -> a`.
               | WriteMutVar -- ^ `forall d a. MutVar# d a -> a -> State# d -> State# d`.

               -- Errors
               | Error
               | Undefined
               deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Primitive

-- | Literals for denoting unwrapped types such as Int#, Double#.
data Lit = LitInt Integer
         | LitFloat Float
         | LitDouble Double
         | LitRational Rational
         | LitBV [Int] -- ^ Variable size bitvector- exists primarily to interact with SMT solver
         | LitChar Char
         | LitString String
         | LitInteger Integer
         deriving (Show, Read, Generic, Typeable, Data)

instance Hashable Lit

integerToBV :: Int -- ^ Width
            -> Integer -- ^ Value
            -> Lit
integerToBV w i = LitBV $ map (\pos -> if testBit i pos then 1 else 0) [w - 1,w-2..0]

bvToInteger :: [Int] -> Integer
bvToInteger bv = foldl' (\acc (i,b) -> if b == 1 then setBit acc i else acc)
                 0
                 (zip [length bv - 1, length bv - 2..0] bv)

-- | When comparing Lits, we treat LitFloat and LitDouble specially, to ensure reflexivity,
-- even in the case that we have NaN.
instance Eq Lit where
    LitInt x == LitInt y = x == y
    LitFloat x == LitFloat y | isNaN x, isNaN y = True
                             | otherwise = x == y
    LitDouble x == LitDouble y | isNaN x, isNaN y = True
                               | otherwise = x == y
    LitRational x == LitRational y = x == y
    LitBV x == LitBV y = x == y
    LitChar x == LitChar y = x == y
    LitString x == LitString y = x == y
    LitInteger x == LitInteger y = x == y
    _ == _ = False

-- | Data constructor.
-- The existential and universal quantifiers should correspond to the TyForAll's binders.
-- In particular,
--   @univTyVar dc ++ existTyVar dc == leadingTyForAllBindings dc@
data DataCon = DataCon { dc_name :: Name 
                       , dc_type :: Type 
                       , dc_univ_tyvars :: [Id] -- ^ Universal type variables
                       , dc_exist_tyvars :: [Id] -- ^ Existential type variables
                       } deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

instance Hashable DataCon

-- | Extract the `Name` of a `DataCon`.
dcName :: DataCon -> Name
dcName (DataCon n _ _ _) = n

-- | Describe the conditions to match on a particular `Alt`.
data AltMatch = DataAlt DataCon [Id] -- ^ Match a datacon. The number of `Id`s
                                     -- must match the number of term arguments
                                     -- for the datacon.
              | LitAlt Lit
              | Default
              deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable AltMatch

-- | `Alt`s consist of the `AltMatch` that is used to match
-- them, and the `Expr` that is evaluated provided that the `AltMatch`
-- successfully matches.
data Alt = Alt { altMatch :: AltMatch, altExpr :: Expr } deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Alt

-- | Concrete evidence of the equality or compatibility of two types.
data Coercion = Type :~ Type deriving (Eq, Show, Read, Generic, Typeable, Data)

instance Hashable Coercion

-- | Types information.
data Type = TyVar Id -- ^ Polymorphic type variable.
          | TyLitInt -- ^ Unwrapped primitive Int type.
          | TyLitFloat -- ^ Unwrapped primitive Float type.
          | TyLitDouble -- ^ Unwrapped primitive Int type.
          | TyLitBV Int -- ^ Unwrapped primitive BitVector type of the indicated width.
          | TyLitRational -- ^ Unwrapped primitive Rational type.
          | TyLitChar -- ^ Unwrapped primitive Int type.
          | TyLitString -- ^ Unwrapped primitive String type.
          | TyFun Type Type -- ^ Function type. For instance (assume Int): \x -> x + 1 :: TyFun TyInt TyInt
          | TyApp Type Type -- ^ Application of a type.
          | TyCon Name Kind -- ^ Type constructor for a concrete type
          | TyForAll Id Type -- ^ Introduces a type variable.
          | TyBottom -- ^ Type for erroring/non-terminating expressions.
          | TYPE
          | TyUnknown
          deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

-- | A `Kind` is a t`Type` of a t`Type`.
type Kind = Type

instance Hashable Type

-- | A `Tickish` allows storing extra information in a `Tick`.
data Tickish = Breakpoint Span -- ^ A breakpoint for the GHC Debugger
             | HpcTick !Int T.Text -- ^ A tick used by HPC to track each subexpression in the original source code.
                                   --
                                   -- Together, the `Int` identifier and the Module Name indicate a unique location.
             | NamedLoc Name -- ^ A G2 specific tick, intended to allow,
                             -- in concert with a @`G2.Execution.Reducer.Reducer`@, for domain
                             -- specific modifications to a
                             -- @`G2.Language.Support.State`@'s tracking field.
             deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Tickish

-- | Represents a rewrite rule
data RewriteRule = RewriteRule { ru_name :: T.Text
                               , ru_module :: T.Text
                               , ru_head :: Name
                               , ru_rough :: [Maybe Name]
                               , ru_bndrs :: [Id]
                               , ru_args :: [Expr]
                               , ru_rhs :: Expr } deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable RewriteRule

-- | Represents a function call, with it's arguments and return value as Expr
data FuncCall = FuncCall { funcName :: Name
                         , arguments :: [Expr]
                         , returns :: Expr } deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable FuncCall
