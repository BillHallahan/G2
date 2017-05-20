-- | Transforms
--   The idea behind the G2/Core directory is that it should provide the
--   specifications necessary of a semi-advanced simply typed lambda calculus
--   language. However, the directory itself should not contain an actual
--   implementation of an evaluator for this STLC. Instead, the Transforms
--   module aims to support basic operations on these STLC execution states,
--   such as expression lookup, bindings, renaming, etc.
module G2.Core.Transforms where

import qualified Data.Map as M

import           G2.Core.Language


exprBind :: Name -> Expr -> State -> State
exprBind name expr state = state {expr_env = eenv'}
  where eenv' = M.insert name expr (expr_env state)

exprBindList :: [(Name, Expr)] -> State -> State
exprBindList binds state = foldl (\s (n, e) -> exprBind n e s) state binds

exprLookup :: Name -> State -> Maybe Expr
exprLookup name state = M.lookup name (expr_env state)

-- | Free Variables
--   Find the free variables of a particular state's current expression, and
--   return a list of the names that are free.
--
--   Note that we overapproximate the list of free variables we find. Consider:
--
--     Case m_exp
--          [((..., ["a1", "a2"]), alt_expr1)
--          ,((..., ["b1", "b2"]), alt_expr2)]
--          alt_exprs_ty
--
--   It is possible for "b1" and "b2" to be free variables within alt_expr1,
--   and for "a1" and "a2" to be free variables in alt_expr2. This brings us to
--   the question of whether we should over approximate free variables (i.e.
--   consider all ["a1", "a2", "b1", "b2"]) or under approximate (i.e. return
--   only those that are free across all the Alts). Since freeVars will mostly
--   be used to create conflict lists when trying to find fresh variable names,
--   it is thus a better design choice for us to over approximate.
freeVars :: State -> [Name]
freeVars state = case curr_expr state of
    -- If it does not appear in the environment, then it is free.
    Var n t -> if exprLookup n state == Nothing then [n] else []

    -- The lambda's binder is added to the expr_env for this branch of the tree
    -- traversal; its mapping is arbitrary since we only need it to exist in
    -- order to demonstrate a lack of freedom for successive appearances of b.
    Lam b e t -> let state' = exprBind b BAD state  -- BAAAAAAAD practice :)
                 in freeVars (state' {curr_expr = e})

    App f a -> let lhs = freeVars (state {curr_expr = f})
                   rhs = freeVars (state {curr_expr = a})
               in lhs ++ rhs
    
    -- As in the example above, we over approximate freeness in a Case's Alts.
    Case e as t -> let altFrees ((dc, params), aexp) =
                         let binds  = zip params (repeat BAD)
                             state' = state {curr_expr = aexp}  -- Go into Alt.
                         in freeVars (exprBindList binds state')
                   in concatMap altFrees as

    -- Const, DCon, Type, BAD
    _ -> []

