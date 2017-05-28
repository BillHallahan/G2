-- | Engine
--   The symbolic execution engine. Many hours were spent on improving this.
module G2.SymbolicExecution.Engine where

import qualified Data.List as L
import qualified Data.Map  as M

import G2.Core.Language
import G2.Core.Transforms

-- We return values from evaluations. A value is defined as something that a
-- program may return from running. The only oddity here may be that we allow
-- lambda expressions to be returned from evaluation.
isVal :: State -> Bool
isVal state = case curr_expr state of
    Var n _ -> exprLookup n state == Nothing
    App (Lam _ _ _) _ -> False
    App f a -> isVal (state {curr_expr = f}) && isVal (state {curr_expr = a})
    Case _ _ _ -> False
    _ -> True

-- | Expression Type
--   Yields the type of a G2 Core Expression.
exprType :: Expr -> Type
exprType (Var _ t) = t
exprType (Const (CInt _))    = TyRawInt
exprType (Const (CFloat _))  = TyRawFloat
exprType (Const (CDouble _)) = TyRawDouble
exprType (Const (CChar _))   = TyRawChar
exprType (Const (CString _)) = TyRawString
exprType (Const (COp _ t))   = t
exprType (Lam _ _ t) = t
exprType (DCon (DC (n,_,t,a))) = foldl1 (\b r -> TyFun r b) (reverse a ++ [t])
exprType (Case _ _ t) = t
exprType (Type t) = t
exprType (BAD) = TyBottom
exprType (App f a) = case exprType f of {TyFun l r->r; t->TyApp t (exprType a)}

-- | Stepper
--   We run our program in discrete steps.
step :: State -> [State]
step state = case curr_expr state of
  -- We treat unbounded free variables as symbolic during evaluation.
  Var n t -> case exprLookup n state of
      Nothing -> [state]
      Just ex -> [state {curr_expr = ex}]

  -- App-Lam expressions are a concrete example of function application.
  App (Lam b lx t) ae -> let b' = freshSeededName b state
                             lx_state = rename b b' (state {curr_expr = lx})
                         in [exprBind b' ae lx_state]

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
               shares = map (\s -> (curr_expr s,path_cons s,sym_links s)) asts
           in [ast {curr_expr = App f (curr_expr ast)} | ast <- asts]
      else let fsts = step (state {curr_expr = f})
               shares = map (\s -> (curr_expr s,path_cons s,sym_links s)) fsts
           in [fst {curr_expr = App (curr_expr fst) a} | fst <- fsts]

  -- Case-Case
  Case (Case m1 as1 t1) as2 t2 ->
      let shoveIn :: (Alt, Expr) -> (Alt, Expr)
          shoveIn (Alt (dc, params), ae) = (Alt (dc, params), Case ae as2 t2)
      in [state {curr_expr = Case m1 (map shoveIn as1) t2}]

  -- Case expressions
  Case m as t ->
      let unApp :: Expr -> [Expr]
          unApp (App f a) = unApp f ++ [a]
          unApp expr = [expr]

          isAltxDef :: (Alt, Expr) -> Bool
          isAltxDef (Alt (DC ("DEFAULT", _, TyBottom, []), []), _) = True
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
          doNondef (Alt (dc, params), aexp) =
              let (d:args) = unApp m
              in case d of
                  Var f t -> let params' = freshSeededNameList params state
                                 zipd = zip params params'
                                 pc' = [(m, Alt (dc, params'), True)] ++
                                       path_cons state
                             in [renameList zipd (state { curr_expr = aexp
                                                        , path_cons = pc' })]

                  DCon md -> if length args == length params && dc == md
                      then let params' = freshSeededNameList params state
                               binds = zip params' args
                               zp = zip params params'
                               pc' = [(m, Alt (dc, params'), True)] ++
                                     path_cons state
                               a_st = renameList zp (state { curr_expr = aexp
                                                           , path_cons = pc' })
                           in [exprBindList binds a_st]
                      else []

                  _ -> [state {curr_expr = BAD}]  -- NUH UH NUH!!

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

  -- Const, Lam, DCon, Type, BAD
  _ -> [state]


