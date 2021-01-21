module G2.Equiv.InitRewrite (initWithRHS) where

import G2.Language
import qualified G2.Language.ExprEnv as E

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