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
primType UNeg = TyBottom
primType Assert = TyBottom
primType Assume = TyBottom

-- | `Type` of `Lit`.
litType :: Lit -> Type
litType (LitInt _) = TyLitInt
litType (LitFloat _) = TyLitFloat
litType (LitDouble _) = TyLitDouble
litType (LitChar _)   = TyLitChar
litType (LitString _) = TyLitString
litType (LitBool _) = TyBool

-- | `Type` of `DataCon`.
dataConType :: DataCon -> Type
dataConType (DataCon _ ty tys) = foldr TyFun ty tys
dataConType (PrimCon I) = TyFun TyLitInt TyInt
dataConType (PrimCon D) = TyFun TyLitDouble TyDouble
dataConType (PrimCon F) = TyFun TyLitFloat TyFloat
dataConType (PrimCon C) = TyFun TyLitChar TyChar
dataConType (PrimCon B) = TyBool

-- | `Type` of `Alt`.
altType :: Alt -> Type
altType (Alt _ _ expr) = exprType expr

-- | Expression Type
--   Gets the type of an expression.
exprType :: Expr -> Type
exprType (Var vid) = idType vid
exprType (Prim prim) = primType prim
exprType (Lit lit) = litType lit
exprType (Data dcon) = dataConType dcon
exprType (App fxpr axpr) = TyApp (exprType fxpr) (exprType axpr)
exprType (Lam b expr ) = TyFun (idType b) (exprType expr)
exprType (Let _ expr) = exprType expr
exprType (Case _ _ (a:_)) = altType a
exprType (Type ty) = ty
exprType _ = TyBottom

