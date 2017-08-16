-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( module G2.Internals.Language.Typing
    ) where

import G2.Internals.Language.Syntax

-- | Typeable typeclass.
class Typeable a where
    typeOf :: a -> Type


-- | `Id` instance of `Typeable`.
instance Typeable Id where
    typeOf (Id _ ty) = ty

-- | `Primitive` instance of `Typeable`
instance Typeable Primitive where
    typeOf Ge = TyBottom  -- TODO: fill in correctly.
    typeOf Gt = TyBottom
    typeOf Eq = TyBottom
    typeOf Lt = TyBottom
    typeOf Le = TyBottom
    typeOf And = TyBottom
    typeOf Or = TyBottom
    typeOf Not = TyBottom
    typeOf Implies = TyBottom
    typeOf Plus = TyBottom
    typeOf Minus = TyBottom
    typeOf Mult = TyBottom
    typeOf Div = TyBottom
    typeOf UNeg = TyBottom
    typeOf Assert = TyBottom
    typeOf Assume = TyBottom

-- | `Lit` instance of `Typeable`.
instance Typeable Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitBool _) = TyBool

-- | `DataCon` instance of `Typeable`.
instance Typeable DataCon where
    typeOf (DataCon _ ty tys) = foldr TyFun ty tys
    typeOf (PrimCon I) = TyFun TyLitInt TyInt
    typeOf (PrimCon D) = TyFun TyLitDouble TyDouble
    typeOf (PrimCon F) = TyFun TyLitFloat TyFloat
    typeOf (PrimCon C) = TyFun TyLitChar TyChar
    typeOf (PrimCon B) = TyBool

-- | `Alt` instance of `Typeable`.
instance Typeable Alt where
    typeOf (Alt _ expr) = typeOf expr

-- | `Expr` instance of `Typeable`.
instance Typeable Expr where
    typeOf (Var vid) = typeOf vid
    typeOf (Prim prim) = typeOf prim
    typeOf (Lit lit) = typeOf lit
    typeOf (Data dcon) = typeOf dcon
    typeOf (App fxpr axpr) = TyApp (typeOf fxpr) (typeOf axpr)
    typeOf (Lam b expr ) = TyFun (typeOf b) (typeOf expr)
    typeOf (Let _ expr) = typeOf expr
    typeOf (Case _ _ (a:_)) = typeOf a
    typeOf (Type ty) = ty
    typeOf _ = TyBottom

