-- | Language
--   Provides the language definition of G2. Should not be confused with Core
--   Haskell, although design imitates Core Haskell closely.
module G2.Internals.Language.Syntax
    ( module G2.Internals.Language.Syntax
    ) where

-- | The occurrence name is defined as a string, with a `Maybe` module name
-- appearing. The `Int` denotes a `Unique` translated from GHC. For instance,
-- in the case of @Map.empty@, the occurrence name is @"empty"@, while the
-- module name is some variant of @Just \"Data.Map\"@.
data Name = Name String (Maybe String) Int deriving (Show, Eq, Read, Ord)

data Id = Id Name Type deriving (Show, Eq, Read)

-- | Expressions
--   We annotate our expressions with types. The reason we do this is because
--   type information is needed to reconstruct statements for SMT solvers.
--
-- Var    -- Variables.
-- Lit    -- Literals, such as Int#, +#, and others.
-- Prim   -- A primitive that we have some sort of special support for in the SMT solver.
-- Data   -- Data constructors.
-- App    -- Expression (function) application.
-- Lam    -- Lambda functions. Its type is a TyFun.
-- Let    -- Bindings of Id's to Expr.
-- Case   -- Case expressions. Type denotes the type of its Alts.
-- Type   -- A type expression. Unfortuantely we do need this.
data Expr = Var Id
          | Lit Lit
          | Prim Primitive
          | Data DataCon
          | App Expr Expr
          | Lam Id Expr
          | Let [(Id, Expr)] Expr
          | Case Expr Id [Alt]
          | Type Type
          deriving (Show, Eq, Read)

-- | Primitives
-- These are used to represent various functions in expressions
-- Translations from functions. This allows for more general
-- handling in the SMT solver- we are not tied to the specific function
-- names/symbols that come from Haskell
data Primitive = Ge | Gt | Eq | Lt | Le
               | And | Or | Not | Implies
               | Plus | Minus | Mult | Div
               | Assert | Assume
               deriving (Show, Eq, Read)

-- Lit's are used in the Expr Lit to denote a constant value.
data Lit = LitInt Int
         | LitFloat Rational
         | LitDouble Rational
         | LitChar Char
         | LitString String
         | LitBool Bool
         deriving (Show, Eq, Read)

-- LitCon's are used in DataCons to construct a value of a specific type
data LitCon = I | D | F | C | B deriving (Show, Eq, Read)

data DataCon = DataCon Name Type [Type]
             | PrimCon LitCon
             deriving (Show, Eq, Read)

data AltCon = DataAlt DataCon
            | LitAlt Lit
            | Default
            deriving (Show, Eq, Read)

data Alt = Alt AltCon [Id] Expr deriving (Show, Eq, Read)

data TyBinder = AnonTyBndr
              | NamedTyBndr Name
              deriving (Show, Eq, Read)

-- | Types
--   We need a way of representing types, and so it is done here.
--
--   The TyRaw* types are meant to deal with unwrapped types. For example, Int#
--   would be equivalent to TyRawInt.
--
--   TyApp is a catch-all statement in case we accidentally run into type
--   variables when trying to "type check" a function type's App spine.
--
--   TyConApp is equivalent to applying types to parametrized ADTs:
--
--     data Tree a = Node a | Branch (Tree a) (Tree a)
--     
--     foo :: Tree Int -> Int
--
--   Here the first parameter of foo would have something akin to:
--
--     TyConApp Tree [Int]
--
--   TyBottom is a default filler for when we don't have anything better to do.
data Type = TyVar Name
          | TyInt | TyFloat | TyDouble | TyChar | TyString | TyBool
          | TyLitInt | TyLitFloat | TyLitDouble | TyLitChar | TyLitString
          | TyFun Type Type
          | TyApp Type Type
          | TyConApp TyCon [Type]
          | TyForAll TyBinder Type
          | TyBottom
          deriving (Show, Eq, Read)

data TyCon = TyCon Name deriving (Show, Eq, Read)