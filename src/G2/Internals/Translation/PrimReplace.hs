-- | PrimitiveReplacer

module G2.Internals.Translation.PrimReplace
    (primReplace) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

primReplace :: (ASTContainer m Expr, ASTContainer m Type) => m -> m
primReplace = modifyASTs (primReplaceT) . modifyASTs (primReplace')

primReplace' :: Expr -> Expr
primReplace' (App (Var (Id n t)) a1) = primReplace1 n t a1
primReplace' (App (App (Var (Id n t)) a1) a2) = primReplace2 n t a1 a2
primReplace' (App (App (App (App (Var (Id n t)) a1) a2) a3) a4) = primReplace4 n t a1 a2 a3 a4
primReplace' e = e

primReplace1 :: Name -> Type -> Expr -> Expr
primReplace1 (Name "!" _ _) _ e = App (Prim Not) e
primReplace1 (Name "-" _ _) _ e = App (Prim UNeg) e
primReplace1 n t e1 = App (Var (Id n t)) e1

primReplace2 :: Name -> Type -> Expr -> Expr -> Expr
primReplace2 (Name "&&" _ _) _ e1 e2 = App (App (Prim And) e1) e2
primReplace2 (Name "||" _ _) _ e1 e2 = App (App (Prim Or) e1) e2
primReplace2 n t e1 e2 = App (App (Var (Id n t)) e1) e2

primReplace4 :: Name -> Type -> Expr -> Expr -> Expr -> Expr -> Expr
primReplace4 (Name ">=" _ _) _ _ _ a3 a4  = App (App (Prim Ge) a3) a4
primReplace4 (Name ">" _ _) _ _ _ a3 a4  = App (App (Prim Gt) a3) a4
primReplace4 (Name "==" _ _) _ _ _ a3 a4  = App (App (Prim Eq) a3) a4
primReplace4 (Name "/=" _ _) _ _ _ a3 a4  = App (Prim Not) (App (App (Prim Eq) a3) a4)
primReplace4 (Name "<" _ _) _ _ _ a3 a4  = App (App (Prim Lt) a3) a4
primReplace4 (Name "<=" _ _) _ _ _ a3 a4  = App (App (Prim Le) a3) a4
primReplace4 (Name "+" _ _) _ _ _ a3 a4  = App (App (Prim Plus) a3) a4
primReplace4 (Name "-" _ _) _ _ _ a3 a4  = App (App (Prim Minus) a3) a4
primReplace4 (Name "*" _ _) _ _ _ a3 a4  = App (App (Prim Mult) a3) a4
primReplace4 (Name "/" _ _) _ _ _ a3 a4  = App (App (Prim Div) a3) a4
primReplace4 n t _ _ a3 a4  = App (App (Var (Id n t)) a3) a4
    
primReplaceT :: Type -> Type
primReplaceT (TyConApp (Name "Int" _ _) _) = TyInt
primReplaceT (TyConApp (Name "Double" _ _) _) = TyDouble
primReplaceT (TyConApp (Name "Float" _ _) _) = TyFloat
primReplaceT (TyConApp (Name "Char" _ _) _) = TyChar
primReplaceT (TyConApp (Name "Bool" _ _) _) = TyBool
primReplaceT t = t
