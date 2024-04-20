{-# LANGUAGE FlexibleContexts #-}

-- | Allows substituting rationals for floating points.
module G2.Initialization.FpToRational (substRational) where

import G2.Language

substRational :: (ASTContainer m Expr, ASTContainer m Type) => m -> m
substRational = substRationalPrim . substRationalType

substRationalPrim :: ASTContainer m Expr => m -> m
substRationalPrim = modifyASTs go
    where
        go (Lit (LitFloat f)) = Lit (LitRational $ toRational f)
        go (Lit (LitDouble d)) = Lit (LitRational $ toRational d)
        go (Prim p t) = Prim (substPrim p) t
        go (Case e i t as) = Case e i t $ map substAlt as
        go e = e

substPrim :: Primitive -> Primitive
substPrim FpNeg = Negate
substPrim FpAdd = Plus
substPrim FpSub = Minus
substPrim FpMul = Mult
substPrim FpDiv = Div
substPrim FpLeq = Le
substPrim FpLt = Lt
substPrim FpGeq = Ge
substPrim FpGt = Gt
substPrim FpEq = Eq
substPrim FpNeq = Neq
substPrim FpSqrt = Sqrt
substPrim IntToFloat = IntToRational
substPrim IntToDouble = IntToRational
substPrim p = p

substAlt :: Alt -> Alt
substAlt (Alt (LitAlt (LitFloat f )) e) = Alt (LitAlt (LitRational $ toRational f)) e
substAlt (Alt (LitAlt (LitDouble d )) e) = Alt (LitAlt (LitRational $ toRational d)) e
substAlt a = a

substRationalType :: ASTContainer m Type => m -> m
substRationalType = modifyASTs go
    where
        go TyLitFloat = TyLitRational
        go TyLitDouble = TyLitRational
        go t = t