-- | PrimReplacer

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Preprocessing.PrimReplace (primReplace) where

import G2.Internals.Core.Language
import G2.Internals.Core.AST

primReplace :: (ASTContainer m Expr) => m -> m
primReplace = modifyASTs primReplace'

primReplace' :: Expr -> Expr
primReplace' (App (Var n t) a1) = primReplace1 n t a1
primReplace' (App (App (Var n t) a1) a2) = primReplace2 n t a1 a2
primReplace' (App (App (App (App (Var n t) a1) a2) a3) a4) = primReplace4 n t a1 a2 a3 a4
primReplace' e = e

primReplace1 :: Name -> Type -> Expr -> Expr
primReplace1 (Name "!" _) t e = App (Prim Not t) e
primReplace1 n t e1 = App (Var n t) e1

primReplace2 :: Name -> Type -> Expr -> Expr -> Expr
primReplace2 (Name "&&" _) t e1 e2 = App (App (Prim And t) e1) e2
primReplace2 (Name "||" _) t e1 e2 = App (App (Prim Or t) e1) e2
primReplace2 n t e1 e2 = App (App (Var n t) e1) e2

primReplace4 :: Name -> Type -> Expr -> Expr -> Expr -> Expr -> Expr
primReplace4 (Name f u) t a1 a2 a3 a4
    | f == ">=" && isIDF a1 = App (App (Prim GE t') a3) a4
    | f == ">" && isIDF a1 = App (App (Prim GrT t') a3) a4
    | f == "==" && isIDF a1 = App (App (Prim EQL t') a3) a4
    | f == "/=" && isIDF a1 = App (Prim Not TyBottom) (App (App (Prim EQL t') a3) a4)
    | f == "<" && isIDF a1 = App (App (Prim LsT t') a3) a4
    | f == "<=" && isIDF a1 = App (App (Prim LE t') a3) a4

    | f == "+" && isIDF a1 = App (App (Prim Plus t') a3) a4
    | f == "-" && isIDF a1 = App (App (Prim Minus t') a3) a4
    | f == "*" && isIDF a1 = App (App (Prim Mult t') a3) a4
    | f == "/" && isIDF a1 = App (App (Prim Div t') a3) a4
    | otherwise = App (App (App (App (Var (Name f u) t) a1) a2) a3) a4
    where
        t' = case t of
            TyFun _ t'' -> t''
            TyForAll _ (TyFun _ t'') -> t''
            _ -> TyBottom

        isIDF :: Expr -> Bool
        isIDF (Type (TyConApp (Name "Int" 0) [])) = True
        isIDF (Type (TyConApp (Name "Double" 0) [])) = True
        isIDF (Type (TyConApp (Name "Float" 0) [])) = True
        isIDF t = False
