-- | Transforms
--   The idea behind the G2/Core directory is that it should provide the
--   specifications necessary of a semi-advanced simply typed lambda calculus
--   language. However, the directory itself should not contain an actual
--   implementation of an evaluator for this STLC. Instead, the Transforms
--   module aims to support basic operations on these STLC execution states,
--   such as expression lookup, bindings, renaming, etc.
module G2.Core.Transforms where

import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map  as M

import G2.Core.Language


-- | Expression Binding
--   Bind a (Name, Expr) pair into the expression environment of a state.
exprBind :: Name -> Expr -> State -> State
exprBind name expr state = state {expr_env = eenv'}
  where eenv' = M.insert name expr (expr_env state)

-- | Expression Binding List
--   Bind a whole list of them.
exprBindList :: [(Name, Expr)] -> State -> State
exprBindList binds state = foldl (\s (n, e) -> exprBind n e s) state binds

-- | Expression Lookup
--   Did we find???
exprLookup :: Name -> State -> Maybe Expr
exprLookup name state = M.lookup name (expr_env state)

-- | All Names
--   Returns all the names used in a state. We aggressively over approximate
--   because this function will mostly be used for conflict listing when making
--   fresh variable names -- hence it is safe to do so :)
allNames :: State -> [Name]
allNames state = L.nub (tenvs ++ eenvs ++ cexps ++ pcs ++ slts ++ fints)
  where tenvs = concatMap (\(n, t) -> [n] ++ tys t) (M.toList $ type_env state)
        eenvs = concatMap (\(n, e) -> [n] ++ exs e) (M.toList $ expr_env state)
        cexps = exs $ curr_expr state
        pcs   = concatMap (\(e, a, b) -> exs e ++ alts a) (path_cons state)
        slts  = concatMap (\(a,(b,t,m)) -> [a, b]) (M.toList $ sym_links state)
        fints = concatMap (\(a,(b,i)) -> [a,b]) (M.toList $ func_interps state)

        -- Names in a data constructor.
        dcs (dc_n, _, t, ps) = [dc_n] ++ tys t ++ concatMap tys ps

        -- Names in a type.
        tys (TyVar n) = [n]
        tys (TyFun t1 t2) = tys t1 ++ tys t2
        tys (TyApp tf ta) = tys tf ++ tys ta
        tys (TyConApp n ts) = [n] ++ concatMap tys ts
        tys (TyAlg n ds) = [n] ++ concatMap dcs ds
        tys (TyForAll n t) = [n] ++ tys t
        tys _ = []

        -- Names in an alt.
        alts (dc, params) = dcs dc ++ params

        -- Names in an (Alt, Expr) pair.
        altxs ((dc, params), aexp) = dcs dc ++ params ++ exs aexp

        -- Names in an expression.
        exs (Var n t) = [n] ++ tys t
        exs (Const (COp n t)) = [n] ++ tys t
        exs (Lam b e t) = [b] ++ exs e ++ tys t
        exs (App f a) = exs f ++ exs a
        exs (DCon dc) = dcs dc
        exs (Case m as t) = exs m ++ concatMap altxs as ++ tys t
        exs (Type t) = tys t
        exs _ = []

-- | Fresh Name
--   Generates a fresh name given a state. Default seed is "f$".
freshName :: State -> Name
freshName = freshSeededName "f$"

-- | Fresh Seeded Name
--   We want this new name to be different from all other names in the state.   
--
--   The procedure for generating a new name consists of stripping each element
--   of the conflicts list down to their purely numerical components, and then
--   finding the maximum value. We then take this value +1 as the new number to
--   append to our seed value, after stripping the seed of its numbers.
freshSeededName :: Name -> State -> Name
freshSeededName seed state = stripped_seed ++ show (max_confs_num + 1)
  where conflicts = allNames state
        max_confs_num = L.maximum $ 0:(map nameNum conflicts)
        stripped_seed = filter (not . C.isDigit) seed
        nameNum name = case filter C.isDigit name of
                           [] -> 0
                           xs -> read xs :: Integer

-- | Fresh Seeded Name List
--   Given a list of seeds, generate a list of freshnames for them.
freshSeededNameList :: [Name] -> State -> [Name]
freshSeededNameList seeds state = fst $ foldl freshAndBind ([], state) seeds
  where freshAndBind (acc, st) sd = let sd'  = freshSeededName sd st
                                        acc' = acc ++ [sd']
                                        st'  = exprBind sd' BAD st  -- Conflict
                                    in (acc', st')
-- | Rename
--   Rename all variables of form (Var n) with (Var n').

