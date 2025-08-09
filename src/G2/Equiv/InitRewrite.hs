module G2.Equiv.InitRewrite (initWithRHS, initWithLHS) where

import G2.Execution.Memory
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.TyVarEnv as TV
import qualified G2.Language.Expr as X

import Data.List

import Debug.Trace

initWithRHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithRHS s b r =
  let
      (eenv', tv_env') = updateExprEnvAndTyVarEnv (ru_bndrs r) (expr_env s) (tyvar_env s)
      s' = s {
             curr_expr = CurrExpr Evaluate (ru_rhs r)
           , expr_env = eenv'
           , tyvar_env = tv_env'
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
    Just f -> let t = T.typeOf (tyvar_env s) f
                  i = Id f_name t
                  v = Var i
                  app = X.mkApp (v:ru_args r)
                  (eenv', tv_env') = updateExprEnvAndTyVarEnv (ru_bndrs r) (expr_env s) (tyvar_env s)
                  s' = s {
                         curr_expr = CurrExpr Evaluate app
                       , expr_env = eenv'
                       , tyvar_env = tv_env'
                       }
                  b' = b { input_names = map idName $ ru_bndrs r }
              in
              (markAndSweepPreserving emptyMemConfig s' b', b')

updateExprEnvAndTyVarEnv :: [Id] -> ExprEnv -> TyVarEnv -> (ExprEnv, TyVarEnv)
updateExprEnvAndTyVarEnv is eenv tv_env =
    let
        (ty_is, v_is) = partition (hasTYPE . typeOf tv_env) is
    in
    (foldr E.insertSymbolic eenv v_is, foldr TV.insertSymbolic tv_env ty_is)