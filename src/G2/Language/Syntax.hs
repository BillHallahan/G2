{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

-- Defines most of the central language in G2. This language closely resembles Core Haskell.
-- The central datatypes are `Expr` and `Type`.
module G2.Language.Syntax
    ( module G2.Language.Syntax
    ) where

import GHC.Generics (Generic)
import Data.Data
import Data.Hashable
import qualified Data.Text as T

-- | The native GHC definition states that a `Program` is a list of `Binds`.
-- This is used only in the initial stages of the translation from GHC Core.
-- We quickly shift to using a `State`.
type Program = [Binds]

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

-- | Pairing of a `Name` with a `Type`
data Id = Id Name Type deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

instance Hashable Id

-- | Indicates the purpose of the a Lambda binding
data LamUse = TermL -- ^ Binds at the term level 
            | TypeL -- ^ Binds at the type level
            deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable LamUse

idName :: Id -> Name
idName (Id name _) = name

idType :: Id -> Type
idType (Id _ t) = t
 
{-| This is the main data type for our expression language.

 1. @`Var` `Id`@ is a variable.  Variables may be bound by a `Lam`, `Let`
 or `Case` `Expr`, or be bound in the `ExprEnv`.  A variable may also be
 free (unbound), in which case it is symbolic

 2. @`Lit` `Lit`@ denotes a literal.

 3. @`Data` `DataCon`@ denotes a Data Constructor

 4. @`App` `Expr` `Expr`@ denotes function application.
    For example, the function call:

     @ f x y @
    would be represented as

     @ `App`
       (`App`
         (`Var` (`Id` (`Name` "f" Nothing 0 Nothing) (`TyFun` t (`TyFun` t t))))
         (`Var` (`Id` (`Name` "x" Nothing 0 Nothing) t))
       )
       (`Var` (`Id` (`Name` "y" Nothing 0 Nothing) t)) @

 5. @`Lam` `LamUse` `Id` `Expr`@ denotes a lambda function.
    The `Id` is bound in the `Expr`.
    This binding may be on the type type or term level, depending on the `LamUse`.

 6. @`Case` e i as@ splits into multiple `Alt`s (Alternatives),
    Depending on the value of @e@.  In each Alt, the `Id` @i@ is bound to @e@.
    The `Alt`s must always be exhaustive- there should never be a case where no `Alt`
    can match a given `Expr`.

 7. @`Type` `Type`@ gives a `Expr` level representation of a `Type`.
    These only ever appear as the arguments to polymorphic functions,
    to determine the `Type` bound to type level variables.

 8. @`Cast` e (t1 `:~` t2)@ casts @e@ from the type @t1@ to @t2@
    This requires that @t1@ and @t2@ have the same representation.

 9. @`Coercion` `Coercion`@ allows runtime passing of `Coercion`s to `Cast`s.

 10. @`Tick` `Tickish` `Expr`@ records some extra information into an `Expr`.

 11. @`NonDet` [`Expr`] gives a nondeterministic choice between multiple options
     to continue execution with.

 12. @`SymGen` `Type`@ evaluates to a fresh symbolic variable of the given type.

 13. @`Assume` b e@ takes a boolean typed expression @b@,
     and an expression of arbitrary type @e@.
     During exectuion, @b@ is reduced to SWHNF, and assumed.
     Then, execution continues with @b@.

 14. @`Assert` fc b e@ is similar to `Assume`, but asserts the @b@ holds.
     The `Maybe` `FuncCall` allows us to optionally indicate that the
     assertion is related to a specific function. -}
data Expr = Var Id
          | Lit Lit
          | Prim Primitive Type
          | Data DataCon
          | App Expr Expr
          | Lam LamUse Id Expr
          | Let Binds Expr
          | Case Expr Id [Alt]
          | Type Type
          | Cast Expr Coercion
          | Coercion Coercion
          | Tick Tickish Expr
          | NonDet [Expr]
          | SymGen Type
          | Assume (Maybe FuncCall) Expr Expr
          | Assert (Maybe FuncCall) Expr Expr
          deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

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
data Primitive = Ge
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
               | Plus
               | Minus
               | Mult
               | Div
               | DivInt
               | Quot
               | Mod
               | Rem
               | Negate
               | SqRt
               | IntToFloat
               | IntToDouble
               | FromInteger
               | ToInteger
               | ToInt
               | Error
               | Undefined
               | BindFunc
               deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable Primitive

-- | Literals for denoting unwrapped types such as Int#, Double#.
data Lit = LitInt Integer
         | LitFloat Rational
         | LitDouble Rational
         | LitChar Char
         | LitString String
         | LitInteger Integer
         deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable Lit

-- | Data constructor.
data DataCon = DataCon Name Type deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

instance Hashable DataCon

-- | AltMatches.
data AltMatch = DataAlt DataCon [Id] -- ^ Match a datacon. The number of `Id`s
                                     -- must match the number of term arguments
                                     -- for the datacon.
              | LitAlt Lit
              | Default
              deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable AltMatch

-- | `Alt`s consist of the `AltMatch` that is used to match
-- them, and the `Expr` that is evaluated provided that the `AltMatch`
-- successfully matches.
data Alt = Alt AltMatch Expr deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable Alt

altMatch :: Alt -> AltMatch
altMatch (Alt am _) = am

-- | Used in the `TyForAll`, to bind an `Id` to a `Type`
data TyBinder = AnonTyBndr Type
              | NamedTyBndr Id
              deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

instance Hashable TyBinder

data Coercion = Type :~ Type deriving (Eq, Show, Ord, Read, Generic, Typeable, Data)

instance Hashable Coercion

-- | Types are decomposed as follows:
-- * Type variables correspond to the aliasing of a type
-- * TyLitInt, TyLitFloat etc denote unwrapped primitive types.
-- * Function type. For instance (assume Int): \x -> x + 1 :: TyFun TyInt TyInt
-- * Application, often reducible: (TyApp (TyFun TyInt TyInt) TyInt) :: TyInt
-- * Type constructor (see below) application creates an actual type
-- * For all types
-- * BOTTOM
data Type = TyVar Id
          | TyLitInt 
          | TyLitFloat 
          | TyLitDouble
          | TyLitChar 
          | TyLitString
          | TyFun Type Type
          | TyApp Type Type
          | TyCon Name Kind
          | TyForAll TyBinder Type
          | TyBottom
          | TYPE
          | TyUnknown
          deriving (Show, Eq, Read, Generic, Typeable, Data, Ord)

type Kind = Type

instance Hashable Type

data Tickish = Breakpoint Span -- ^ A breakpoint for the GHC Debugger
             | NamedLoc Name -- ^ A G2 specific tick, intended to allow,
                             -- in concert with a @`Reducer`@, for domain
                             -- specific modifications to a
                             -- @`State`@'s tracking field.
             deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable Tickish

-- | Represents a rewrite rule
data RewriteRule = RewriteRule { ru_name :: T.Text
                               , ru_head :: Name
                               , ru_rough :: [Maybe Name]
                               , ru_bndrs :: [Id]
                               , ru_args :: [Expr]
                               , ru_rhs :: Expr } deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable RewriteRule

-- | Represents a function call, with it's arguments and return value as Expr
data FuncCall = FuncCall { funcName :: Name
                         , arguments :: [Expr]
                         , returns :: Expr } deriving (Show, Eq, Ord, Read, Generic, Typeable, Data)

instance Hashable FuncCall
