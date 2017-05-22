module G2.SymbolicExecution.Engine where

import qualified Data.List as L
import qualified Data.Map  as M

import G2.Core.Language
import G2.Core.Transforms

-- | Value Check
--   We return values from evaluations. A value is defined as something that a
--   program may return from running. The only oddity here may be that we allow
--   lambda expressions to be returned from program evaluation.
isVal :: State -> Bool
isVal state = case curr_expr state of
    Var n _ -> exprLookup n state == Nothing
    App (Lam _ _ _) _ -> False
    App f a -> isVal (state {curr_expr = f}) && isVal (state {curr_expr = a})
    Case _ _ _ -> False
    _ -> True

-- | Stepper
--   We run our program in discrete steps.
step :: State -> [State]
step state = case curr_expr state of
  -- We treat unbounded free variables as symbolic during evaluation.
  Var n t -> case exprLookup n state of
      Nothing -> [state]
      Just ex -> [state {curr_expr = ex}]

  -- App-Lam expressions are a concrete example of function application.
  App (Lam b lx t) ax -> let b' = freshSeededName b' state
                             lx_state = rename b b' (state {curr_expr = lx})
                         in [exprBind b' ax lx_state]

  -- Favor LHS evaluation during Apps to emulate lazy evaluation.
  -- Caveat: LHS and RHS should have independent environments. The two sides
  -- should only share the PC, and SLTs.
  App f a -> if isVal (state {curr_expr = f})
      then let asts = step (state {curr_expr = a})
               shares = map (\s -> (curr_expr s,path_cons s,sym_links s)) asts
           in [state { curr_expr = App f a'
                     , path_cons = pc'
                     , sym_links = M.union (sym_links state) slt' } |
               (a', pc', slt') <- shares]
      else let fsts = step (state {curr_expr = f})
               shares = map (\s -> (curr_expr s,path_cons s,sym_links s)) fsts
           in [state { curr_expr = App f' a
                     , path_cons = pc'
                     , sym_links = M.union (sym_links state) slt' } |
               (f', pc', slt') <- shares]

  -- Case-Case
  Case (Case m1 as1 t1) as2 t2 ->
      let shoveIn :: (Alt, Expr) -> (Alt, Expr)
          shoveIn ((dc, params), ae) = ((dc, params), Case ae as2 t2)
      in [state {curr_expr = Case m1 (map shoveIn as1) t2}]

  -- Case expressions
  Case m as t ->
      let unApp :: Expr -> [Expr]
          unApp (App f a) = unApp f ++ [a]
          unApp expr = [expr]

          isAltxDef :: (Alt, Expr) -> Bool
          isAltxDef ((("DEFAULT", _, TyBottom, []), []), _) = True
          isAltxDef altx = False

          -- For each non-default Alt, we return a singleton list if the match
          -- is possible, and an empty list otherwise. Nice hack, eh? :^)
          --
          -- There are two possible non-error cases for how the matching
          -- expression's App spine might unwind:
          --   [Var n t, ...]
          --     In this case we are dealing with a symbolic function, and we
          --     need only ensure that all the Alt expression arguments are
          --     mapped to unique symbolic (free) variables.
          --
          --   [DCon md, ...]
          --     In this case we first check to see if the data consturctor is
          --     even structurally feasible. If so, we strip off the parameters
          --     and arguments, and bind them into the env of the new Alt state
          --     after renaming the Alt's parameters to ensure uniqueness with
          --     respect to the environment that came before.
          doNondef :: (Alt, Expr) -> [State]
          doNondef ((dc, params), aexp) =
              let (d:args) = unApp m
              in case d of
                  Var f t -> let params' = freshSeededNameList params state
                                 zipd = zip params params'
                             in [renameList zipd (state {curr_expr = aexp})]

                  DCon md -> if length args == length params && dc == md
                      then let params' = freshSeededNameList params state
                               zp = zip params params'
                               pc' = [(m,(md,params'),True)] ++ path_cons state
                               a_st = renameList zp (state { curr_expr = aexp
                                                           , path_cons = pc' })
                               binds = zip params' args
                           in [exprBindList binds a_st]
                      else []

                  _ -> [state {curr_expr = BAD}]  -- NUH UH NUH!!

          -- The DEFAULT case is actually pretty simple: since DEFAULT takes no
          -- parameters, we don't need to care about renaming. Instead, we need
          -- to only make sure that we treat a DEFAULT's PC as the negation of
          -- all the non-DEFAULT's matching conditions.
          doDef :: [(Alt, Expr)] -> (Alt, Expr) -> [State]
          doDef ndfs ((dc, params), aexp) =
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

  -- Const, Lam, DCon, Type, BAD
  _ -> [state]


