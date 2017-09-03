-- | PrimitiveReplacer

module G2.Internals.Translation.PrimReplace
    (primReplace) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

primReplace :: (ASTContainer m Expr, ASTContainer m Type) => m -> m
primReplace = modifyASTs (primReplaceT) . modifyASTs (primReplace')

primReplace' :: Expr -> Expr
primReplace' e = e
{-
primReplace' (Var (Id (Name "!" _ _) _)) = Prim Not
primReplace' (Var (Id (Name "-" _ _) _)) = Prim UNeg
primReplace' (Var (Id (Name "&&" _ _) _)) = Prim And
primReplace' (Var (Id (Name "||" _ _) _)) = Prim Or
primReplace' (Var (Id (Name ">=" _ _) _)) = Prim Ge
primReplace' (Var (Id (Name ">" _ _) _)) = Prim Gt
primReplace' (Var (Id (Name "==" _ _) _)) = Prim Eq
primReplace' (Var (Id (Name "/=" _ _) _)) = Prim Neq
primReplace' (Var (Id (Name "<" _ _) _)) = Prim Lt
primReplace' (Var (Id (Name "<=" _ _) _)) = Prim Le
primReplace' (Var (Id (Name "+" _ _) _)) = Prim Plus
primReplace' (Var (Id (Name "-" _ _) _)) = Prim Minus
primReplace' (Var (Id (Name "*" _ _) _)) = Prim Mult
primReplace' (Var (Id (Name "/" _ _) _)) = Prim Div
primReplace' e = e
-}

primReplaceT :: Type -> Type
primReplaceT t = t

{-
primReplaceT (TyConApp (Name "Int" _ _) _) = TyInt
primReplaceT (TyConApp (Name "Double" _ _) _) = TyDouble
primReplaceT (TyConApp (Name "Float" _ _) _) = TyFloat
primReplaceT (TyConApp (Name "Char" _ _) _) = TyChar
primReplaceT (TyConApp (Name "Bool" _ _) _) = TyBool
primReplaceT t = t
-}
