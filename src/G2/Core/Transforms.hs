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
        dcs :: DataCon -> [Name]
        dcs (DC (dc_n, _, t, ps)) = [dc_n] ++ tys t ++ concatMap tys ps

        -- Names in a type.
        tys :: Type -> [Name]
        tys (TyVar n) = [n]
        tys (TyFun t1 t2) = tys t1 ++ tys t2
        tys (TyApp tf ta) = tys tf ++ tys ta
        tys (TyConApp n ts) = [n] ++ concatMap tys ts
        tys (TyAlg n ds) = [n] ++ concatMap dcs ds
        tys (TyForAll n t) = [n] ++ tys t
        tys _ = []

        -- Names in an alt.
        alts :: Alt -> [Name]
        alts (Alt (dc, params)) = dcs dc ++ params

        -- Names in an (Alt, Expr) pair.
        altxs :: (Alt, Expr) -> [Name]
        altxs (Alt (dc, params), aexp) = dcs dc ++ params ++ exs aexp

        -- Names in an expression.
        exs :: Expr -> [Name]
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

        nameNum :: Name -> Int
        nameNum name = case filter C.isDigit name of
                           [] -> 0
                           xs -> read xs :: Int

-- | Fresh Seeded Name List
--   Given a list of seeds, generate a list of freshnames for them.
freshSeededNameList :: [Name] -> State -> [Name]
freshSeededNameList seeds state = fst $ foldl freshAndBind ([], state) seeds
  where freshAndBind :: ([Name], State) -> Name -> ([Name], State)
        freshAndBind (acc, st) sd =
            let sd'  = freshSeededName sd st
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
    -- then of course need to fold this function over all the Alts. The reason
    -- that we fold instead of map is because this allows us to keep track of
    -- a list of previously processed Alts. Because of this, we can leverage
    -- those previous Alts to make a conflict lists that guarantees the SLTs of
    -- each Alt state will be mutually exclusive in terms of new terms added.
    -- This allows us to union them safely without worry.
    --
    -- Internally, this altState function takes a acc history list and the
    -- current Alt with its expression pair. We construct a state that takes
    -- into account the previous history (does not matter that the expression
    -- environment is messed up from this because we do not use the Alts'
    -- expression environments). From here on, like with the Lam bindings, we
    -- check if the old exists in the params, and then again for the new (the
    -- existence of which will warrant the remapping via renameList).
    --
    -- Finally, we must merge together the symbolic links.
    Case m as t ->
        let altState :: [State] -> (Alt, Expr) -> [State]
            altState acc (Alt (dc, params), aexp) =
              let acc_alls = concatMap allNames acc  -- Super slow :)
                  c_env = M.fromList $ zip acc_alls (repeat BAD)
                  alt_st = state { expr_env = M.union (expr_env state) c_env
                                 , curr_expr = aexp }
              in if old `elem` params
                then acc ++ [alt_st]
                else if new `elem` params
                  then let params' = freshSeededNameList params alt_st
                           zipd = zip params params'
                           alt_st' = renameList zipd alt_st
                           aexp' = curr_expr alt_st'
                           slk' = sym_links alt_st'
                       in acc ++ [rename old new (alt_st' { curr_expr = aexp'
                                                          , sym_links = slk' })]
                  else acc ++ [rename old new alt_st]

            joinSLTs :: [SymLinkTable] -> SymLinkTable
            joinSLTs slts = foldl M.union M.empty slts
            
            m_state = rename old new (state {curr_expr = m})
            alt_states = foldl altState [] as
            alt_state_alts = map (\((Alt (dc, params), _), a_state) ->
                                      (Alt (dc, params), curr_expr a_state))
                                 (zip as alt_states)
            slts = joinSLTs $ [sym_links m_state] ++ (map sym_links alt_states)
        in state { curr_expr = Case (curr_expr m_state) alt_state_alts t
                 , sym_links = slts }
    _ -> state

-- | Rename List
--   Rename, but with a list instead. If we pipe in the input from some fresh
--   seeded name list, we are guaranteed to have uniqueness at least, such that
--   the remaps don't step over on each other.
renameList :: [(Name, Name)] -> State -> State
renameList remaps state = foldl (\s (n, n') -> rename n n' s) state remaps

