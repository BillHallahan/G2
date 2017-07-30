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
primType PTRUE    = TyBool
primType PFALSE   = TyBool
primType PGE      = Bottom  -- TODO: fill in correctly.
primType PGT      = Bottom
primType PEQ      = Bottom
primType PLT      = Bottom
primType PLE      = Bottom
primType PAND     = Bottom
primType POR      = Bottom
primType PNOT     = Bottom
primType PImplies = Bottom
primType PPlus    = Bottom
primType PMinus   = Bottom
primType PMult    = Bottom
primType PDiv     = Bottom
primType PAssert  = Bottom
primType PAssume  = Bottom

-- | `Type` of `Literal`.
litType :: Literal -> Type
litType (LitInt _)    = TyLitInt
litType (LitFloat _)  = TyLitFloat
litType (LitDouble _) = TyLitDouble
litType (LitChar _)   = TyLitChar
litType (LitString _) = TyLitString

-- | `Type` of `DataCon`.
dataconType :: DataCon -> Type
dataconType (DataCon _ ty tys) = foldr TyFun ty tys
dataconType (PrimDataCon pd)   = case pd of
    I      -> TyFun TyLitInt TyInt
    D      -> TyFun TyLitDouble TyDouble
    F      -> TyFun TyLitFloat TyFloat
    C      -> TyFun TyLitChar TyChar
    PTrue  -> TyBool
    PFalse -> TyBool

-- | `Type` of `Alt`.
altType :: Alt -> Type
altType (Alt _ _ expr) = exprType expr

-- | Expression Type
--   Gets the type of an expression.
exprType :: Expr -> Type
exprType (Var id)         = idType id
exprType (Prim prim)      = primType prim
exprType (Lit lit)        = litType lit
exprType (Data dcon)      = dataconType dcon
exprType (App fxpr axpr)  = TyApp (exprType fxpr) (exprType axpr)
exprType (Lam id expr)    = TyFun (idType id) (exprType expr)
exprType (Let bnd expr)   = exprType expr
exprType (Case _ _ (a:_)) = altType a
exprType (Type ty)        = ty
exprType _                = Bottom

