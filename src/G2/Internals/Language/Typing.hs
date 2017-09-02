-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( module G2.Internals.Language.Typing
    ) where

import G2.Internals.Language.Syntax

-- | Typed typeclass.
class Typed a where
    typeOf :: a -> Type


-- | `Id` instance of `Typed`.
instance Typed Id where
    typeOf (Id _ ty) = ty

-- | `Primitive` instance of `Typed`
instance Typed Primitive where
    typeOf Ge = TyBottom  -- TODO: fill in correctly.
    typeOf Gt = TyBottom
    typeOf Eq = TyBottom
    typeOf Lt = TyBottom
    typeOf Le = TyBottom
    typeOf And = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Or = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Not = TyFun TyBool TyBool
    typeOf Implies = TyFun TyBool (TyFun TyBool TyBool)
    typeOf Plus = TyBottom
    typeOf Minus = TyBottom
    typeOf Mult = TyBottom
    typeOf Div = TyBottom
    typeOf UNeg = TyBottom

-- | `Lit` instance of `Typed`.
instance Typed Lit where
    typeOf (LitInt _) = TyLitInt
    typeOf (LitFloat _) = TyLitFloat
    typeOf (LitDouble _) = TyLitDouble
    typeOf (LitChar _)   = TyLitChar
    typeOf (LitString _) = TyLitString
    typeOf (LitBool _) = TyBool

-- | `DataCon` instance of `Typed`.
instance Typed DataCon where
    typeOf (DataCon _ ty tys) = foldr TyFun ty tys
    typeOf (PrimCon I) = TyFun TyLitInt TyInt
    typeOf (PrimCon D) = TyFun TyLitDouble TyDouble
    typeOf (PrimCon F) = TyFun TyLitFloat TyFloat
    typeOf (PrimCon C) = TyFun TyLitChar TyChar
    typeOf (PrimCon B) = TyBool

-- | `Alt` instance of `Typed`.
instance Typed Alt where
    typeOf (Alt _ expr) = typeOf expr

-- | `Expr` instance of `Typed`.
instance Typed Expr where
    typeOf (Var vid) = typeOf vid
    typeOf (Prim prim) = typeOf prim
    typeOf (Lit lit) = typeOf lit
    typeOf (Data dcon) = typeOf dcon
    typeOf (App fxpr axpr) = TyApp (typeOf fxpr) (typeOf axpr)
    typeOf (Lam b expr) = TyFun (typeOf b) (typeOf expr)
    typeOf (Let _ expr) = typeOf expr
    typeOf (Case _ _ (a:_)) = typeOf a
    typeOf (Type ty) = ty
    typeOf (Assert _ e) = typeOf e
    typeOf (Assume _ e) = typeOf e

    typeOf _ = TyBottom

