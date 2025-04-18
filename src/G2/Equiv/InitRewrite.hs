module G2.Equiv.InitRewrite (initWithRHS, initWithLHS) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.Expr as X

import G2.Execution.Memory

initWithRHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithRHS s b r =
  let s' = s {
             curr_expr = CurrExpr Evaluate (ru_rhs r)
           , expr_env = foldr E.insertSymbolic (expr_env s) (ru_bndrs r)
           }
      b' = b { input_names = map idName $ ru_bndrs r }
  in
  (markAndSweepPreserving emptyMemConfig s' b', b')

initWithLHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithLHS s b r =
  -- make LHS into a single expr
  let f_name = ru_head r
      f_maybe = E.lookup f_name (expr_env s)
  in
  case f_maybe of
    Nothing -> error "function name not found"
    Just f -> let t = T.typeOf f
                  i = Id f_name t
                  v = Var i
                  app = X.mkApp (v:ru_args r)
                  s' = s {
                         curr_expr = CurrExpr Evaluate app
                       , expr_env = foldr E.insertSymbolic (expr_env s) (ru_bndrs r)
                       }
                  b' = b { input_names = map idName $ ru_bndrs r }
              in
              (markAndSweepPreserving emptyMemConfig s' b', b')
