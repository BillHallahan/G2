-- | Type Checker
--   Provides type checking capabilities over G2 Core.
module G2.Internals.Core.TypeChecker where

import G2.Internals.Core.Language

import qualified Data.List as L

-- | Expression Type
--   Gets the type of an expression.
exprType :: Expr -> Type
exprType (Var _ t) = t
exprType (Const (CInt _))    = TyRawInt
exprType (Const (CFloat _))  = TyRawFloat
exprType (Const (CDouble _)) = TyRawDouble
exprType (Const (CChar _))   = TyRawChar
exprType (Const (CString _)) = TyRawString
exprType (Const (COp _ t))   = t
exprType (Lam _ _ t) = t
exprType (Let _ e) = exprType e
exprType (App f a) = case exprType f of {TyFun l r->r; t->TyApp t (exprType a)}
exprType (Data (DataCon _ _ t a)) = L.foldl1 (\b r->TyFun r b) (reverse a++[t])
exprType (Data DEFAULT) = TyBottom
exprType (Case _ _ t) = t
exprType (Type t) = t
exprType (Assume c e) = exprType e
exprType (Assert c e) = exprType e
exprType (BAD) = TyBottom

-- | Type Check a State
--   Check that a given State is valid.
typeCheck :: State -> Bool
typeCheck state = undefined

