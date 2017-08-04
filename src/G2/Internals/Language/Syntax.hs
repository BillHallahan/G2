module G2.Internals.Language.Syntax
    ( module G2.Internals.Language.Syntax
    ) where

-- | The occurrence name is defined as a string, with a `Maybe` module name
-- appearing. The `Int` denotes a `Unique` translated from GHC. For instance,
-- in the case of @Map.empty@, the occurrence name is @"empty"@, while the
-- module name is some variant of @Just \"Data.Map\"@.
data Name = Name String (Maybe String) Int deriving (Show, Eq, Read, Ord)

data Id = Id Name Type deriving (Show, Eq, Read)

data Expr = Var Id
          | Lit Lit
          | Prim Primitive
          | Data DataCon
          | App Expr Expr
          | Lam Id Expr
          | Let Bind Expr
          | Case Expr Id [Alt]
          | Type Type
          | BLACKHOLE
          deriving (Show, Eq, Read)

data Primitive = PTrue | PFalse
               | Ge | Gt | Eq | Lt | Le
               | And | Or | Not | Implies
               | Plus | Minus | Mult | Div
               | Assert | Assume
               deriving (Show, Eq, Read)

data Lit = LitInt Int
         | LitFloat Rational
         | LitDouble Rational
         | LitChar Char
         | LitString String
         deriving (Show, Eq, Read)

data DataCon = DataCon Name Type [Type]
             | PrimCon LitCon
             deriving (Show, Eq, Read)

data LitCon = I | D | F | C | CTrue | CFalse deriving (Show, Eq, Read)

data RecForm = Rec | NonRec deriving (Show, Eq, Read)

data Bind = Bind RecForm [(Id, Expr)] deriving (Show, Eq, Read)

data AltCon = DataAlt DataCon
            | Default
            deriving (Show, Eq, Read)

data Alt = Alt AltCon [Id] Expr deriving (Show, Eq, Read)

data TyBinder = AnonTyBndr
              | NamedTyBndr Name
              deriving (Show, Eq, Read)

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

