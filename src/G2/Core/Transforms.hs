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
rename :: Name -> Name -> State -> State
rename old new state = case curr_expr state of
    -- If it matches, we update, and add an entry to the symbolic link table.
    Var n t -> let sym_links' = M.insert new (old,t,Nothing) (sym_links state) 
               in if n == old
                 then state { curr_expr = Var new t, sym_links = sym_links'}
                 else state

    -- Stop adding things if the lambda's binder shadows the old name, as the
    -- transformation would be completely redundant otherwise. However, if the
    -- new name is equal to the current lambda binder, we need to completely
    -- replace the lambda expression first before proceeding.
    --
    -- To do this, we first make a completely different b as b', which makes it
    -- so that b == new, but b' /= new. Following this we rename all instances
    -- of b to b' within the lambda's body. Then we are safe :)
    Lam b e t -> if old == b
                   then state
                   else if new == b
                     then let b' = freshSeededName b state  -- b' /= new
                              state' = rename b b' (state {curr_expr = e})
                              e' = curr_expr state'
                              sym_links' = sym_links state'
                          in rename old new (state' { curr_expr = Lam b' e' t
                                                    , sym_links = sym_links' })
                     else let state' = rename old new (state {curr_expr = e})
                          in state { curr_expr = Lam b (curr_expr state') t
                                   , sym_links = sym_links state' }

    -- This is more straightforward than Lam. Branch and union the sym links.
    App f a -> let lhs = rename old new (state {curr_expr = f})
                   rhs = rename old new (state {curr_expr = a})
               in state { curr_expr = App (curr_expr lhs) (curr_expr rhs)
                        , sym_links = M.union (sym_links lhs) (sym_links rhs) }

    -- This is annoying and complicated. For each alt, we do the same check as
    -- we did for the lambda case, since Alts are semantically equivalent to
    -- multi-argument function applications. Thankfully there was foresight to
    -- write a exprBindList function :)
    --
    -- First we apply a rename on the matching expression.
    --
    -- Then we have a function that makes a new renamed state for each Alt. We
    -- then of course need to map this function over all the Alts. Internally,
    -- this function examines whehter or not the old name exists in the params
    -- of the data constructor. As with in the Lam case, if the old is, we just
    -- return the state as is. If it is not, and the new is instead one of the
    -- params, we must perform a renaming of all (or just the one) of the names
    -- within the rest of the alt expression. This guarantees lack of conflict
    -- and allows us to recursively call rename again once we have "adjusted"
    -- the current state accordingly.
    --
    -- Finally, we must merge together the symbolic links 
    {-
    Case m as t ->
        let m_state = rename old new (state {curr_expr = m})
            altState ((dc, params), aexp) =
              if old `elem` params
                then state {curr_expr = aexp}
                else if new `elem` params
                  then let params' = freshSeededNameList params state
                           zipd = zip params params'
                           ae_st' = renameList zipd (state {curr_expr = aexp})
                           aexp' = curr_expr ae_st'
                           sym_links' = sym_links ae_st'
                       in rename old new (ae_st' { curr_expr = aexp'
                                                 , sym_links = sym_links' })
                  else rename old new (state {curr_expr = aexp})
            alt_states = map altState as
            alt_state_alts = map (\(((dc, params),_), a_state) ->
                                    ((dc, params), curr_expr a_state))
                                 (zip as alt_states)
            combslts slts = foldl M.union M.empty slts  -- Technically a bug.
            slts = combslts $ [sym_links m_state] ++ (map sym_links alt_states)
        in state { curr_expr = Case (curr_expr m_state) alt_state_alts t
                 , sym_links = slts }
    -}
    _ -> state

-- | Rename List
--   Rename, but with a list instead.
renameList :: [(Name, Name)] -> State -> State
renameList = undefined

