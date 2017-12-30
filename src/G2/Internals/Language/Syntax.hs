{-# LANGUAGE DeriveGeneric #-}

-- | Language
--   Provides the language definition of G2. Should not be confused with Core
--   Haskell, although design imitates Core Haskell closely.
module G2.Internals.Language.Syntax
    ( module G2.Internals.Language.Syntax
    ) where

import GHC.Generics (Generic)
import Data.Hashable

-- | The native GHC defintion states that a `Program` is a list of `Binds`.
type Program = [Binds]

-- | Typically `Binds` are categorized as recursive or non-recursive. This is
-- because recursive let bindings require their local scopes of all bindings
-- to contain each other. Technically, all bindings can be expressed as
-- recursive, though GHC differentiates them. We do not care here because we
-- assume naming independence.
type Binds = [(Id, Expr)]

-- | The occurrence name is defined as a string, with a `Maybe` module name
-- appearing. The `Int` denotes a `Unique` translated from GHC. For instance,
-- in the case of @Map.empty@, the occurrence name is @"empty"@, while the
-- module name is some variant of @Just \"Data.Map\"@.
data Name = Name String (Maybe String) Int deriving (Show, Eq, Read, Ord, Generic)

instance Hashable Name

data Id = Id Name Type deriving (Show, Eq, Read, Generic)

instance Hashable Id

idName :: Id -> Name
idName (Id name _) = name

-- | Expressions are defined as:
--   * Variables
--   * Literals such as unwrapped Int# types
--   * Primitive known operation on WRAPPED types such as +, <, etc
--   * Data Constructors
--   * Application of expressions: apply RHS to LHS, LHS being a function
--   * Lambda expressions where the `Id` is the lambda binder
--   * Let bindings such that `Binds` appears in the scope for the body `Expr`
--   * Case pattern matching where `Expr` is inspection, `Id` is binding
--   * Type expression wrappers for who knows what
data Expr = Var Id
          | Lit Lit
          | Prim Primitive Type
          | Data DataCon
          | App Expr Expr
          | Lam Id Expr
          | Let Binds Expr
          | Case Expr Id [Alt]
          | Type Type
          | Cast Expr Coercion
          | Coercion Coercion
          | Assume Expr Expr
          | Assert Expr Expr
          deriving (Show, Eq, Read, Generic)

instance Hashable Expr

-- | Primitives
-- | These enumerate a set of known, and G2-augmented operations, over wrapped
-- data types such as Int, Char, Double, etc. We refer to these as primitives.
-- We further introduce a assertion and assumption as special features.
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
               | Negate
               | Error
               | Undefined
               deriving (Show, Eq, Read, Generic)

instance Hashable Primitive

-- | Literals for denoting unwrapped types such as Int#, Double#. These would
-- be contained within primitives.
data Lit = LitInt Int
         | LitFloat Rational
         | LitDouble Rational
         | LitChar Char
         | LitString String
         deriving (Show, Eq, Read, Generic)

instance Hashable Lit

-- | Data constructor. We have a special ditinction for primitive types.
data DataCon = DataCon Name Type [Type] deriving (Show, Eq, Read, Generic)

instance Hashable DataCon

-- | Alternative case constructors, which are done by structural matching,
-- which is a phrase I invented to describe this. In essence, consider the
-- following scenario:
--    case expr of
--       Con1 -> ...
--       Con2 -> ...
-- We define structural matching as when the expr matches to either Con1 or
-- Con2. Unlike traditional true / false matching in imperative languages,
-- structural matching is more general and is data constructor matching.
data AltMatch = DataAlt DataCon [Id]
              | LitAlt Lit
              | Default
              deriving (Show, Eq, Read, Generic)

instance Hashable AltMatch

-- | Alternatives consist of the consturctor that is used to structurally match
-- onto them, a list of parameters corresponding to this constructor, which
-- serve to perform binding in the environment scope. The `Expr` is what is
-- evaluated provided that the `AltMatch` successfully matches.
data Alt = Alt AltMatch Expr deriving (Show, Eq, Read, Generic)

instance Hashable Alt

altMatch :: Alt -> AltMatch
altMatch (Alt am _) = am

-- | TyBinder is used only in the `TyForAll` and `AlgDataTy`
data TyBinder = AnonTyBndr Type
              | NamedTyBndr Id
              deriving (Show, Eq, Read, Generic)

instance Hashable TyBinder

data Coercion = Type :~ Type deriving (Eq, Show, Read, Generic)

instance Hashable Coercion

-- | Types are decomposed as follows:
-- * Type variables correspond to the aliasing of a type
-- * TyInt, TyFloat, etc, denote primitive types
-- * TyLitInt, TyLitFloat etc denote unwrapped primitive types.
-- * Function type. For instance (assume Int): \x -> x + 1 :: TyFun TyInt TyInt
-- * Application, often reducible: (TyApp (TyFun TyInt TyInt) TyInt) :: TyInt
-- * Type constructor (see below) application creates an actual type
-- * For all types
-- * BOTTOM
data Type = TyVar Id
          -- | TyInt | TyFloat | TyDouble | TyChar | TyString | TyBool
          | TyLitInt | TyLitFloat | TyLitDouble | TyLitChar | TyLitString
          | TYPE
          | TyFun Type Type
          | TyApp Type Type
          | TyConApp Name [Type]
          | TyForAll TyBinder Type
          | TyBottom
          deriving (Show, Eq, Read, Generic)

instance Hashable Type
