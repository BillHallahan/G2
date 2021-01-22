module G2.Equiv.InitRewrite (initWithRHS, initWithLHS) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.Expr as X

addSymbolic :: Id -> ExprEnv -> ExprEnv
addSymbolic i =
  E.insertSymbolic (idName i) i

initWithRHS :: State t -> RewriteRule -> State t
initWithRHS s r =
  s {
      curr_expr = CurrExpr Evaluate (ru_rhs r)
    , symbolic_ids = ru_bndrs r
    , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
    }

initWithLHS :: State t -> RewriteRule -> State t
initWithLHS s r =
  -- TODO make LHS into a single expr
  let fName = ru_head r
      fMaybe = E.lookup fName (expr_env s)
  in
  case fMaybe of
    Nothing -> error "function name not found"
    Just f -> let t = T.typeOf f
                  -- i = (Id (Name fName Nothing 0 Nothing) t)
                  i = Id fName t
                  v = Var i
              in
              s {
                curr_expr = CurrExpr Evaluate (X.mkApp (v:ru_args r))
              , symbolic_ids = ru_bndrs r
              , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
              }
