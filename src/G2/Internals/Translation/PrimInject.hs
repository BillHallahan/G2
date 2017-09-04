-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

primInject :: ASTContainer p Expr => p -> p
primInject = modifyASTs primInject'

primInject' :: Expr -> Expr
primInject' (Var (Id (Name "!" _ _) _)) = mkNot
primInject' (Var (Id (Name "&&" _ _) _)) = mkAnd
primInject' (Var (Id (Name "||" _ _) _)) = mkOr
primInject' (Var (Id (Name ">=" _ _) _)) = mkGe
primInject' (Var (Id (Name ">" _ _) _)) = mkGt
primInject' (Var (Id (Name "==" _ _) _)) = mkEq
primInject' (Var (Id (Name "/=" _ _) _)) = mkNeq
primInject' (Var (Id (Name "<" _ _) _)) = mkLt
primInject' (Var (Id (Name "<=" _ _) _)) = mkLe
primInject' (Var (Id (Name "+" _ _) _)) = mkPlus
primInject' (Var (Id (Name "-" _ _) _)) = mkMinus
primInject' (Var (Id (Name "*" _ _) _)) = mkMult
primInject' (Var (Id (Name "/" _ _) _)) = mkDiv
primInject' e = e