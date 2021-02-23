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
      (wrapped_expr, ng') = caseWrap (ru_rhs r) ng
      s' = s {
             curr_expr = CurrExpr Evaluate wrapped_expr
           , symbolic_ids = ru_bndrs r
           , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
           }
      b' = b {
             name_gen = ng'
           }
  in
  (s', b')

initWithLHS :: State t -> Bindings -> RewriteRule -> (State t, Bindings)
initWithLHS s b r =
  -- TODO make LHS into a single expr
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
                  (wrapped_expr, ng') = caseWrap app ng
                  s' = s {
                         curr_expr = CurrExpr Evaluate wrapped_expr
                       , symbolic_ids = ru_bndrs r
                       , expr_env = foldr addSymbolic (expr_env s) (ru_bndrs r)
                       }
                  b' = b {
                         name_gen = ng'
                       }
              in
              (s', b')

-- TODO perform the wrapping in here instead
caseWrap :: Expr -> N.NameGen -> (Expr, N.NameGen)
caseWrap e ng =
    -- TODO changed away from TyUnknown
    let (matchId, ng') = N.freshId (typeOf e) ng
        c = Case e matchId [Alt Default (Var matchId)]
    in
    (c, ng')
