-- | Engine
--   The symbolic execution engine. Many hours were spent on improving this.
module G2.Internals.Symbolic.Engine
    ( isValue
    , step  ) where

import G2.Internals.Core

import qualified Data.List as L
import qualified Data.Map  as M

-- | Is Value
--   Is the current expression a value -- i.e. something that we can return?
isValue :: State -> Bool
isValue state = case curr_expr state of
    Var n _ -> lookupExpr n (expr_env state) == Nothing
    Prim _ _ -> True
    App (Lam _ _ _) _ -> False
    App f a -> isValue (state {curr_expr=f}) && isValue (state {curr_expr=a})
    Let _ _ -> False
    Case _ _ _ -> False
    Assume _ _ -> False
    Assert _ _ -> False
    _ -> True

-- | Step Var
--   We treat unbounded free variables as symbolic during evaluation.
stepVar :: State -> ([State], [State])
stepVar state = case lookupExpr n (expr_env state) of
    Nothing -> ([state], [])
    Just ex -> ([state {curr_expr = ex}], [])
  where Var n t = curr_expr state

stepPrim :: State -> ([State], [State])
stepPrim state = ([state], [])

-- | Step Let
stepLet :: State -> ([State], [State])
stepLet state = ([bindExprList bs (state {curr_expr = e})], [])
  where Let bs e = curr_expr state

-- | Step (App Lam Expr)
stepAppLam :: State -> ([State], [State])
stepAppLam state = ([bindExpr b' ae l_st], [])
  where App (Lam b l t) ae = curr_expr state
        (b', st') = freshSeededName b state
        l_st      = renameExpr b b' (st' {curr_expr = l})

-- | Step (App Case Expr)
stepAppCaseF :: State -> ([State], [State])
stepAppCaseF state = ([state {curr_expr = Case m as' t'}], [])
  where App (Case m as t) ae = curr_expr state
        as' = map (\(Alt (dc, pars), x) -> (Alt (dc, pars), App x ae)) as
        t'  = exprType $ snd $ head as'

-- | Step (App Expr Case)
stepAppCaseA :: State -> ([State], [State])
stepAppCaseA state = ([state {curr_expr = Case m as' t'}], [])
  where App fe (Case m as t) = curr_expr state
        as' = map (\(Alt (dc, pars), x) -> (Alt (dc, pars), App fe x)) as
        t'  = exprType $ snd $ head as'

-- | Step App
--   Favor LHS evaluation during Apps to emulate lazy evaluation.
--   We permit environment sharing across the LHS and RHS of the App because
--   our fresh variable finder is overly aggressive, and so this is okay.
stepApp :: State -> ([State], [State])
stepApp state = if isValue (state {curr_expr = f})
    then ([a_st {curr_expr = App f (curr_expr a_st)} | a_st <- a_sts], a_dsts)
    else ([f_st {curr_expr = App (curr_expr f_st) a} | f_st <- f_sts], f_dsts)
  where App f a = curr_expr state
        (f_sts, f_dsts) = step (state {curr_expr = f})
        (a_sts, a_dsts) = step (state {curr_expr = a})

-- | Shove Alts Inwards
shove :: State -> (Alt, Expr) -> (Alt, Expr)
shove state (Alt (dc, params), ae) = (Alt (dc, params), Case ae as2 t2)
  where Case (Case m1 as1 t1) as2 t2 = curr_expr state

-- | Step Case Case
stepCaseCase :: State -> ([State], [State])
stepCaseCase state = ([state {curr_expr = Case m1 (map (shove state) as1) t2}],
                      [])
  where Case (Case m1 as1 t1) as2 t2 = curr_expr state

-- | Flatten App Spine
flattenApp :: Expr -> [Expr]
flattenApp (App f a) = flattenApp f ++ [a]
flattenApp otherwise = [otherwise]

-- | Is Alt DEFAULT Data Constructor
isAltDefault :: (Alt, Expr) -> Bool
isAltDefault (Alt (dc, _), _) = dc == DEFAULT

-- | Do Non-DEFAULT Alt
--   This emulates a state generated by branching on a non-DEFAULT Alt. We
--   return a singleton list if a state is possible, and empty otherwise. Empty
--   states occur when structural matching fails.
doNDef :: State -> (Alt, Expr) -> [State]
doNDef state (Alt (dc, params), aexp) = case d of
    -- If the matching expression is a Var, then we should treat it as a
    -- symbolic function, which means that it returns symbolic results, and
    -- consequently, the data constructor's parameters are now free symbols.
    Var f t -> [renameExprList p_zip (st' { curr_expr = aexp
                                          , path_cons = pcs'})]

    Prim f t -> [renameExprList p_zip (st' { curr_expr = aexp
                                          , path_cons = pcs'})]
    -- If the matching expression is a data constructor that can successfully
    -- perform structural matching, then do usual stuff of binding expressions.
    Data md -> if (length args == length params) && (dc == md)
        then let binds = zip params' args
                 a_st = renameExprList p_zip (st' { curr_expr = aexp
                                                  , path_cons = pcs' })
             in [bindExprList binds a_st]  -- Structural matching failure.
    -- We can only perform Alt matching based on structure or Var!
        else []
    _ -> [state {curr_expr = BAD}]
  where Case m as t = curr_expr state
        (d:args)       = flattenApp m
        (params', st') = freshSeededNameList params state
        p_zip          = zip params params' -- RHS guaranteed to be fresh :)
        pcs'           = [CondAlt m (Alt (dc, params')) True] ++ path_cons st'
        
-- | Do DEFAULT Alt
--   This emulates a state generated by branching on a DEFAULT Alt. Since the
--   DEFAULT takes no parameters ,we don't need to care about renaming. Rather,
--   we need to only make sure that we treat each DEFAULT's PC as the negation
--   of all the non-DEFAULT matching conditions.
doDef :: State -> [(Alt, Expr)] -> (Alt, Expr) -> [State]
doDef state ndfs (Alt (dc, params), aexp) =
    [state {curr_expr = aexp, path_cons = pcs'}]
  where Case m as t = curr_expr state
        neg_alts = map fst ndfs
        neg_pcs  = map (\na -> CondAlt m na False) neg_alts
        pcs'     = (path_cons state) ++ neg_pcs

-- | Step Case
stepCase :: State -> ([State], [State])
stepCase state = if isValue (state {curr_expr = m})
    then (concatMap (doNDef state) nds ++ concatMap (doDef state nds) ds, [])
    else ([m_st {curr_expr = Case (curr_expr m_st) as t} | m_st <- m_sts],dsts)
  where Case m as t = curr_expr state
        nds   = filter (not . isAltDefault) as
        ds    = filter isAltDefault as
        (m_sts, dsts) = step (state {curr_expr = m})

-- | Step Assume
stepAssume :: State -> ([State], [State])
stepAssume state = if isValue (state {curr_expr = exp})
    then case cond of
        -- If the LHS is a Lam, then we apply it, and later on continue left
        -- derivation of the expression until we hit a value term.
        Lam b c t -> ([state {curr_expr = Assume (App cond exp) exp}], [])
        -- If the LHS has already been saturated, evaluate it until value.
        otherwise -> if isValue (state {curr_expr = cond})
          then ([state {curr_expr = exp, path_cons = pcs'}], [])
          else ([c_st{curr_expr=Assume (curr_expr c_st) exp} | c_st<-c_sts],cd)
    else ([e_st {curr_expr=Assume cond (curr_expr e_st)} | e_st <- e_sts], ed)
  where Assume cond exp = curr_expr state
        (c_sts, cd) = step (state {curr_expr = cond})
        (e_sts, ed) = step (state {curr_expr = exp})
        pcs'  = [CondExt cond True] ++ path_cons state
 
-- | Step Assert
stepAssert :: State -> ([State], [State])
stepAssert state = if isValue (state {curr_expr = exp})
    then case cond of
        -- If the LHS is a Lam, then we apply it, and later on continue left
        -- derivation of the expression until we hit a value term.
        Lam b c t -> ([state {curr_expr = Assert (App cond exp) exp}], [])
        -- If the LHS has already been saturated, evaluate it until value.
        otherwise -> if isValue (state {curr_expr = cond})
          then ([state {curr_expr = exp, path_cons = f_pcs}], [])
          else ([c_st {curr_expr = Assert (curr_expr c_st) exp} |
                 c_st <- c_sts], cd)
    else ([e_st {curr_expr = Assert cond (curr_expr e_st)} |
           e_st <- e_sts], ed)
  where Assert cond exp = curr_expr state
        (c_sts, cd) = step (state {curr_expr = cond})
        (e_sts, ed) = step (state {curr_expr = exp})
        t_pcs = [CondExt cond True]  ++ path_cons state
        f_pcs = [CondExt cond False] ++ path_cons state

-- | Stepper
--   We run our program in discrete steps. If confused, please email Anton.
--   Email: antonxue1572@gmail.com, anton.xue@yale.edu
step :: State -> ([State], [State])
step state = if isValue state
    then ([], [state])
    else case curr_expr state of
        Var _ _               -> stepVar      state
        Prim _ _              -> stepPrim     state 
        Let _ _               -> stepLet      state
        App (Lam _ _ _) _     -> stepAppLam   state
        App (Case _ _ _) _    -> stepAppCaseF state
        App _ (Case _ _ _)    -> stepAppCaseA state
        App _ _               -> stepApp      state
        Case (Case _ _ _) _ _ -> stepCaseCase state 
        Case _ _ _            -> stepCase     state
        Assume _ _            -> stepAssume   state
        Assert _ _            -> stepAssert   state
        otherwise             -> ([], [state])

