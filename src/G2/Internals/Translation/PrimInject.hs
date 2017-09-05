-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

primInject :: (ASTContainer p Expr, ASTContainer p Type) => p -> p
primInject = modifyASTs primInjectE

primInjectE :: Expr -> Expr
primInjectE (Var (Id (Name "!" _ _) _)) = mkNot
primInjectE (Var (Id (Name "&&" _ _) _)) = mkAnd
primInjectE (Var (Id (Name "||" _ _) _)) = mkOr
primInjectE (Var (Id (Name ">=" _ _) _)) = mkGe
primInjectE (Var (Id (Name ">" _ _) _)) = mkGt
primInjectE (Var (Id (Name "==" _ _) _)) = mkEq
primInjectE (Var (Id (Name "/=" _ _) _)) = mkNeq
primInjectE (Var (Id (Name "<" _ _) _)) = mkLt
primInjectE (Var (Id (Name "<=" _ _) _)) = mkLe
primInjectE (Var (Id (Name "+" _ _) _)) = mkPlus
primInjectE (Var (Id (Name "-" _ _) _)) = mkMinus
primInjectE (Var (Id (Name "*" _ _) _)) = mkMult
primInjectE (Var (Id (Name "/" _ _) _)) = mkDiv

primInjectE (Var (Id (Name "I#" _ _) _)) = Data $ PrimCon I
primInjectE (Var (Id (Name "D#" _ _) _)) = Data $ PrimCon D
primInjectE (Var (Id (Name "F#" _ _) _)) = Data $ PrimCon F
primInjectE (Var (Id (Name "C#" _ _) _)) = Data $ PrimCon C

primInjectE e = e
