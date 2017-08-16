-- | Type Checker
--   Provides type checking capabilities over G2 Core.
module G2.Internals.Core.TypeChecker
    ( typeOf
    , typeCheck ) where

import G2.Internals.Core.Language

import qualified Data.List as L

-- | Expression Type
--   Gets the type of an expression.
typeOf :: GenExpr a -> GenType a
typeOf (Var _ t) = t
typeOf (Prim _ t) = t
typeOf (Const (CInt _))    = TyRawInt
typeOf (Const (CFloat _))  = TyRawFloat
typeOf (Const (CDouble _)) = TyRawDouble
typeOf (Const (CChar _))   = TyRawChar
typeOf (Const (CString _)) = TyRawString
typeOf (Lam _ _ t) = t
typeOf (Let _ e) = typeOf e
typeOf (App f a) = case typeOf f of {TyFun l r->r; t->TyApp t (typeOf a)}
typeOf (Data (DataCon _ _ t a)) = L.foldl1 (\b r->TyFun r b) (reverse a++[t])
typeOf (Data (PrimCon DTrue)) = TyBool
typeOf (Data (PrimCon DFalse)) = TyBool
typeOf (Data (PrimCon I)) = TyInt
typeOf (Data (PrimCon D)) = TyDouble
typeOf (Data (PrimCon F)) = TyFloat
typeOf (Data (PrimCon C)) = TyChar
typeOf (Data DEFAULT) = TyBottom
typeOf (Case _ _ t) = t
typeOf (Type t) = t
typeOf (Assume _ e) = typeOf e
typeOf (Assert _ e) = typeOf e
typeOf (BAD) = TyBottom

-- | Type Check a State
--   Check that a given State is valid.
typeCheck :: State -> Bool
typeCheck state = undefined

