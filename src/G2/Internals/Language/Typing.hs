-- | Type Checker
--   Provides type checking capabilities over G2 Language.
module G2.Internals.Language.Typing
    ( module G2.Internals.Language.Typing
    ) where

import G2.Internals.Language.Syntax

-- | `Type` of `Id`.
idType :: Id -> Type
idType (Id _ ty) = ty

-- | `Type` of `Primitive`.
primType :: Primitive -> Type
primType PTrue = TyBool
primType PFalse = TyBool
primType Ge = TyBottom  -- TODO: fill in correctly.
primType Gt = TyBottom
primType Eq = TyBottom
primType Lt = TyBottom
primType Le = TyBottom
primType And = TyBottom
primType Or = TyBottom
primType Not = TyBottom
primType Implies = TyBottom
primType Plus = TyBottom
primType Minus = TyBottom
primType Mult = TyBottom
primType Div = TyBottom
primType Assert = TyBottom
primType Assume = TyBottom

-- | `Type` of `Lit`.
litType :: Lit -> Type
litType (LitInt _) = TyLitInt
litType (LitFloat _) = TyLitFloat
litType (LitDouble _) = TyLitDouble
litType (LitChar _)   = TyLitChar
litType (LitString _) = TyLitString

-- | `Type` of `DataCon`.
dataconType :: DataCon -> Type
dataconType (DataCon _ ty tys) = foldr TyFun ty tys
dataconType (PrimCon I) = TyFun TyLitInt TyInt
dataconType (PrimCon D) = TyFun TyLitDouble TyDouble
dataconType (PrimCon F) = TyFun TyLitFloat TyFloat
dataconType (PrimCon C) = TyFun TyLitChar TyChar
dataconType (PrimCon CTrue) = TyBool
dataconType (PrimCon CFalse) = TyBool

-- | `Type` of `Alt`.
altType :: Alt -> Type
altType (Alt _ _ expr) = exprType expr

-- | Expression Type
--   Gets the type of an expression.
exprType :: Expr -> Type
exprType (Var vid) = idType vid
exprType (Prim prim) = primType prim
exprType (Lit lit) = litType lit
exprType (Data dcon) = dataconType dcon
exprType (App fxpr axpr) = TyApp (exprType fxpr) (exprType axpr)
exprType (Lam b expr ) = TyFun (idType b) (exprType expr)
exprType (Let bnd expr) = exprType expr
exprType (Case _ _ (a:_)) = altType a
exprType (Type ty) = ty
exprType _ = TyBottom

