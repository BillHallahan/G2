module G2.Internals.Execution.Common
    ( lookupExpr
    , lookupType
    ) where

import G2.Internals.Language

import qualified Data.Map as M

lookupExpr :: Name -> ExprEnv -> Maybe Expr
lookupExpr name eenv = case M.lookup name eenv of
    Just (Var redir _) -> lookupExpr redir eenv
    mb_expr -> mb_expr

lookupType :: Name -> TypeEnv -> Maybe Type
lookupType name tenv = case M.lookup name tenv of
    Just (TyVar redir) -> lookupType redir tenv
    mb_type -> mb_type

