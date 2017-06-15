-- | Engine
--   The symbolic execution engine. Many hours were spent on improving this.
module G2.Internals.Symbolic.Engine where

import G2.Internals.Core

import qualified Data.List as L
import qualified Data.Map  as M

-- We return values from evaluations. A value is defined as something that a
-- program may return from running. The only oddity here may be that we allow
-- lambda expressions to be returned from evaluation.
isVal :: State -> Bool
isVal state = case curr_expr state of
    Var n _ -> lookupExpr n (expr_env state) == Nothing
    App (Lam _ _ _) _ -> False
    App f a -> isVal (state {curr_expr = f}) && isVal (state {curr_expr = a})
    Let _ _ -> False
    Case _ _ _ -> False
    Spec _ _ -> False
    _ -> True

-- | Stepper
--   We run our program in discrete steps.
step :: State -> [State]
step state = case curr_expr state of
  -- We treat unbounded free variables as symbolic during evaluation.
  Var n t -> case lookupExpr n (expr_env state) of
      Nothing -> [state]
      Just ex -> [state {curr_expr = ex}]

  -- Thankfully this is fairly simple :)
  Let bs e -> [bindExprList bs (state {curr_expr = e})]

  -- App-Lam expressions are a concrete example of function application.
  App (Lam b lx t) ae ->
      let b' = freshSeededName b state
          lx_state = rename b b' (state {curr_expr = lx})
      in [bindExpr b' ae lx_state]

  -- App-Cases are most likely not necessary and can be commented out.
  App (Case m as t) ae ->
      let as' = map (\(Alt (dc, pars), x) -> (Alt (dc, pars), App x ae)) as
          t'  = exprType $ snd $ head as'
      in [state {curr_expr = Case m as' t'}]

  App fe (Case m as t) ->
      let as' = map (\(Alt (dc, pars), x) -> (Alt (dc, pars), App fe x)) as
          t'  = exprType $ snd $ head as'
      in [state {curr_expr = Case m as' t'}]

  -- Favor LHS evaluation during Apps to emulate lazy evaluation.
  -- We permit environment sharing across the LHS and RHS of the App because
  -- our fresh variable finder is overly aggressive, and so this is okay.
  App f a -> if isVal (state {curr_expr = f})
      then let asts = step (state {curr_expr = a})
           in [ast {curr_expr = App f (curr_expr ast)} | ast <- asts]
      else let fsts = step (state {curr_expr = f})
           in [fst {curr_expr = App (curr_expr fst) a} | fst <- fsts]

  -- Case-Case conversions.
  Case (Case m1 as1 t1) as2 t2 ->
      let shoveIn :: (Alt, Expr) -> (Alt, Expr)
          shoveIn (Alt (dc, params), ae) = (Alt (dc, params), Case ae as2 t2)
      in [state {curr_expr = Case m1 (map shoveIn as1) t2}]

  -- Case expressions.
  Case m as t ->
      let unApp :: Expr -> [Expr]
          unApp (App f a) = unApp f ++ [a]
          unApp expr = [expr]

          isAltxDef :: (Alt, Expr) -> Bool
          isAltxDef (Alt (DEFAULT, _), _) = True
          isAltxDef altx = False

          -- Handle non-default Alts. We return a singleton list if a state is
          -- possible, and an empty one if otherwise. Empty states may occur
          -- when data constructors do not successfully structurally match.
          doNondef :: (Alt, Expr) -> [State]
          doNondef (Alt (dc, params), aexp) =
              let (d:args) = unApp m
              in case d of
                  -- If the matching expression is a Var, then we should treat
                  -- it as a symbolic function, which means that it returns
                  -- symbolic results, and consequently, the data constructor's
                  -- parameters must now be set to free variables.
                  Var f t -> let params' = freshSeededNameList params state
                                 zipd = zip params params'
                                 pc' = [(m, Alt (dc, params'), True)] ++
                                       path_cons state
                             in [renameList zipd (state { curr_expr = aexp
                                                        , path_cons = pc' })]

                  -- If the matching expression is a data constructor that can
                  -- successfully perform structural matching, then we do the
                  -- usual stuff like updating PC's, and environment binding.
                  Data md -> if length args == length params && dc == md
                      then let params' = freshSeededNameList params state
                               binds = zip params' args
                               zp = zip params params'
                               pc' = [(m, Alt (dc, params'), True)] ++
                                     path_cons state
                               a_st = renameList zp (state { curr_expr = aexp
                                                           , path_cons = pc' })
                           in [bindExprList binds a_st]

                      -- Structural matching failed.
                      else []

                  -- NUH UH NUH!!
                  _ -> [state {curr_expr = BAD}]

          -- The DEFAULT case is actually pretty simple: since DEFAULT takes no
          -- parameters, we don't need to care about renaming. Instead, we need
          -- to only make sure that we treat a DEFAULT's PC as the negation of
          -- all the non-DEFAULT's matching conditions.
          doDef :: [(Alt, Expr)] -> (Alt, Expr) -> [State]
          doDef ndfs (Alt (dc, params), aexp) =
              let neg_alts = map fst ndfs
                  neg_pcs = map (\na -> (m, na, False)) neg_alts
              in [state { curr_expr = aexp
                        , path_cons = (path_cons state) ++ neg_pcs }]

          nondefs = filter (not . isAltxDef) as
          defs = filter isAltxDef as
      in if isVal (state {curr_expr = m})
          then (concatMap doNondef nondefs) ++ (concatMap (doDef nondefs) defs)
          else let msts = step (state {curr_expr = m})
               in [mst {curr_expr = Case (curr_expr mst) as t} | mst <- msts]

  -- Assertions have two flavors: Either the LHS that denotes the predicate has
  -- been applied, or it is not, and still a lambda. We consider the latter.
  Spec cond exp -> if isVal (state {curr_expr = exp})
      then case cond of
          -- If the LHS is a Lam, then we apply it, and later on continue left
          -- derivation of the expression until it hits a value term.
          Lam b c t -> [state {curr_expr = Spec (App cond exp) exp}]

          -- If the LHS has already been saturated, evaluate it until value.
          otherwise -> if isVal (state {curr_expr = cond})
              then [state { curr_expr = exp
                          , path_cons = [(cond, Alt (DEFAULT, []), True)] ++
                                        path_cons state }]
              else let csts = step (state {curr_expr = cond})
                   in [cst{curr_expr = Spec (curr_expr cst) exp} | cst <- csts]
      else let ests = step (state {curr_expr = exp})
           in [est {curr_expr = Spec cond (curr_expr est)} | est <- ests]

  -- Const, Lam, DCon, Type, BAD
  _ -> [state]


