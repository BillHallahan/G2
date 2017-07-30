-- | PrimReplacer

module G2.Internals.Translation.PrimReplace
    () where

{-
    (primReplace) where

import G2.Internals.Translation.Language
import G2.Internals.Core.AST

primReplace :: (ASTContainer m TExpr, ASTContainer m TType) => m -> m
primReplace = modifyASTs (primReplaceT) . modifyASTs (primReplace')

primReplace' :: TExpr -> TExpr
primReplace' (App (Var n t) a1) = primReplace1 n t a1
primReplace' (App (App (Var n t) a1) a2) = primReplace2 n t a1 a2
primReplace' (App (App (App (App (Var n t) a1) a2) a3) a4) = primReplace4 n t a1 a2 a3 a4
primReplace' e = e

primReplace1 :: TName -> TType -> TExpr -> TExpr
primReplace1 ("!", _) t e = App (Prim Not t) e
primReplace1 n t e1 = App (Var n t) e1

primReplace2 :: TName -> TType -> TExpr -> TExpr -> TExpr
primReplace2 ("&&", _) t e1 e2 = App (App (Prim And t) e1) e2
primReplace2 ("||", _) t e1 e2 = App (App (Prim Or t) e1) e2
primReplace2 n t e1 e2 = App (App (Var n t) e1) e2

primReplace4 :: TName -> TType -> TExpr -> TExpr -> TExpr -> TExpr -> TExpr
primReplace4 f t a1 a2 a3 a4
    | fst f == ">=" && isIDF a1 = App (App (Prim GE t') a3) a4
    | fst f == ">" && isIDF a1 = App (App (Prim GrT t') a3) a4
    | fst f == "==" && isIDF a1 = App (App (Prim EQL t') a3) a4
    | fst f == "/=" && isIDF a1 = App (Prim Not TyBottom) (App (App (Prim EQL t') a3) a4)
    | fst f == "<" && isIDF a1 = App (App (Prim LsT t') a3) a4
    | fst f == "<=" && isIDF a1 = App (App (Prim LE t') a3) a4

    | fst f == "+" && isIDF a1 = App (App (Prim Plus t') a3) a4
    | fst f == "-" && isIDF a1 = App (App (Prim Minus t') a3) a4
    | fst f == "*" && isIDF a1 = App (App (Prim Mult t') a3) a4
    | fst f == "/" && isIDF a1 = App (App (Prim Div t') a3) a4
    | otherwise = App (App (App (App (Var f t) a1) a2) a3) a4
    where
        t' = case t of
            TyFun _ t'' -> t''
            TyForAll _ (TyFun _ t'') -> t''
            _ -> TyBottom

        isIDF :: TExpr -> Bool
        isIDF (Type (TyConApp ("Int", _) [])) = True
        isIDF (Type (TyConApp ("Double", _) [])) = True
        isIDF (Type (TyConApp ("Float", _) [])) = True
        isIDF t = False

primReplaceT :: TType -> TType
primReplaceT (TyConApp ("Int", _) _) = TyInt
primReplaceT (TyConApp ("Double", _) _) = TyDouble
primReplaceT (TyConApp ("Float", _) _) = TyFloat
primReplaceT (TyConApp ("Char", _) _) = TyChar
primReplaceT (TyConApp ("Bool", _) _) = TyBool
primReplaceT t = t
-}
