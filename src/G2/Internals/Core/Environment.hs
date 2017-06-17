-- | Environment
--   Performs environment bindings and manipulations on State.
module G2.Internals.Core.Environment
    ( lookupExpr
    , lookupType
    , bindExpr
    , bindExprList ) where

import G2.Internals.Core.Language

import qualified Data.Map as M

-- | Expression Lookup
--   Did we find???
lookupExpr :: Name -> EEnv -> Maybe Expr
lookupExpr = M.lookup

-- | Type Lookup
--   ???
lookupType :: Name -> TEnv -> Maybe Type
lookupType = M.lookup

-- | Expression Binding
--   Bind a (Name, Expr) pair into the expression environment of a state.
bindExpr :: Name -> Expr -> State -> State
bindExpr name expr state = state {expr_env = eenv'}
  where eenv' = M.insert name expr (expr_env state)

-- | Expression Binding List
--   Bind a whole list of them.
bindExprList :: [(Name, Expr)] -> State -> State
bindExprList binds state = foldl (\s (n, e) -> bindExpr n e s) state binds

