module G2.Equiv.InitRewrite (initWithRHS, initWithLHS) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.Expr as X

import qualified G2.Language.Naming as N

addSymbolic :: Id -> ExprEnv -> ExprEnv
addSymbolic i =
  E.insertSymbolic (idName i) i

initWithRHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithRHS s b r =
  let ng = name_gen b
      s' = s {
             curr_expr = CurrExpr Evaluate (ru_rhs r)
           , symbolic_ids = ru_bndrs r
           , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
           }
      b' = b { input_names = map idName $ ru_bndrs r }
  in
  (s', b')

initWithLHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithLHS s b r =
  -- make LHS into a single expr
  let fName = ru_head r
      fMaybe = E.lookup fName (expr_env s)
  in
  case fMaybe of
    Nothing -> error "function name not found"
    Just f -> let t = T.typeOf f
                  i = Id fName t
                  v = Var i
                  app = X.mkApp (v:ru_args r)
                  ng = name_gen b
                  s' = s {
                         curr_expr = CurrExpr Evaluate app
                       , symbolic_ids = ru_bndrs r
                       , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
                       }
                  b' = b { input_names = map idName $ ru_bndrs r }
              in
              (s', b')