-- | Renamer
--   Renaming is a hard problem, apparently. This is mainly because we assume
--   an arbitrary case where the names that appear in the expressions are NOT
--   all "fresh" -- that is, it is possible for lambda binders to have a
--   conflicting name with that of the current environment bindings. Thus, we
--   must be careful to avoid accidentally capturing free variables.
module G2.Internals.Core.Renamer
    ( allNames
    , freshSeededName
    , freshSeededNameList
    , rename
    , renameList          ) where

import G2.Internals.Core.AST
import G2.Internals.Core.Environment
import G2.Internals.Core.Language

import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map  as M

-- | All Names
--   Returns all the names used in a state. We aggressively over approximate
--   because this function will mostly be used for conflict listing when making
--   fresh variable names -- hence it is safe to do so :)
allNames :: State -> [Name]
allNames state = L.nub (expr_names ++ type_names ++ eenv_keys ++ tenv_keys)
  where expr_names = evalASTs exs state
        type_names = evalASTs tys state
        eenv_keys = (M.keys . expr_env) state
        tenv_keys = (M.keys . type_env) state

        -- Names from an Expr.
        exs :: Expr -> [Name]
        exs (Var n t)     = [n]
        exs (Const (COp n t)) = [n]
        exs (Lam b e t)   = [b]
        exs (Let bs e)    = map fst bs
        exs (Case m as t) = concatMap (\(Alt (_, ps), _) -> ps) as
        exs _ = []

        -- Names from a Type.
        tys :: Type -> [Name]
        tys (TyVar n)   = [n]
        tys (TyConApp n _) = [n]
        tys (TyAlg n _) = [n]
        tys (TyForAll n _) = [n]
        tys _ = []

-- | Fresh Seeded Name
--   We want this new name to be different from all other names in the state.   
freshSeededName :: Name -> State -> Name
freshSeededName seed state = stripped_seed ++ show (max_confs_num + 1)
  where conflicts = allNames state
        max_confs_num = L.maximum $ 0:(map nameNum conflicts)
        stripped_seed = filter (not . C.isDigit) seed

        -- Highest number sequence in a name, ignoring characters.
        nameNum :: Name -> Int
        nameNum name = case filter C.isDigit name of
                           [] -> 0
                           xs -> read xs :: Int

-- | Fresh Seeded Name List
--   Given a list of seeds, generate a list of freshnames for them. We apply a
--   fold operation in order to keep track of a "history".
freshSeededNameList :: [Name] -> State -> [Name]
freshSeededNameList [] _ = []
freshSeededNameList (n:ns) s = n':freshSeededNameList ns s'
  where n' = freshSeededName n s
        s' = bindExpr n' BAD s  -- Conflict

-- | Join Symbolic Link Tables
-- Can only safely join them if their new entries are disjoint!!
joinSLTs :: [SymLinkTable] -> SymLinkTable
joinSLTs slts = foldl M.union M.empty slts
 
-- | Rename Var
-- If it matches, we update, and add an entry to the symbolic link table.
renameVar :: Name -> Name -> State -> State
renameVar old new state = if n == old
    then state { curr_expr = Var new t, sym_links = slt' }
    else state
  where Var n t = curr_expr state
        slt' = M.insert new (old, t, Nothing) (sym_links state) 

-- | Rename Lam
-- Must check for cases where the lambda's binder might be old or new.
renameLam :: Name -> Name -> State -> State
renameLam old new state = if b == old
    then state  -- Shadowing occurs
    else e_state {curr_expr = Lam b (curr_expr e_state) t}
  where Lam b e t = curr_expr state
        e_state = rename old new (state {curr_expr = e})

-- | Rename Let
renameLet :: Name -> Name -> State -> State
renameLet old new state = if old `elem` b_lhs
    then state  -- Shadowing occurs.
    else e_state { curr_expr = cexpr', sym_links = slt' }
  where Let bs e = curr_expr state
        b_lhs = map fst bs
        b_rhs = map snd bs
        e_state = rename old new (state {curr_expr = e})
        b_sts = tail $ foldl rawFoldFunRHS [("_", e_state)] bs
        slt'  = joinSLTs $ [sym_links e_state] ++ map (sym_links . snd) b_sts
        b_norm = map (\(n, s) -> (n, curr_expr s)) b_sts
        cexpr' = Let b_norm (curr_expr e_state)

        -- When we bind let statements, we have to be aware of potentially
        -- changing symbolic link tables, which is why we fold over states
        -- in order to ensure disjointness when renaming. Only call if old
        -- and new both do not appear in lhs! Super important!! >:(
        rawFoldFunRHS :: [(Name, State)] -> (Name, Expr) -> [(Name, State)]
        rawFoldFunRHS acc (n, bexp) =
            let acc_alls = map fst acc ++ (concatMap allNames (map snd acc))
                c_env = M.fromList $ zip acc_alls (repeat BAD)
                eenv' = M.union (expr_env state) c_env
                b_st  = state { expr_env = eenv', curr_expr = bexp }
            in acc ++ [(n, rename old new b_st)]

-- | Rename App
renameApp :: Name -> Name -> State -> State
renameApp old new state = state_a {curr_expr = App f' a'}
  where App f a = curr_expr state
        state_f = rename old new (state {curr_expr = f})
        state_a = rename old new (state_f {curr_expr = a})
        f' = curr_expr state_f
        a' = curr_expr state_a

-- | Rename Case
renameCase :: Name -> Name -> State -> State
renameCase old new state = state { curr_expr = cexpr', sym_links = slt' }
  where Case m as t = curr_expr state
        -- Renaming the matching expression while we can.
        m_state = rename old new (state {curr_expr = m})
        -- Create the alt states that we can use for merging later. Make
        -- sure to include the m_state, since that may also have new slts!
        -- We take the tail because we need to zip it later. Very precise!
        alt_states = tail $ foldl altState [m_state] as
        -- Extraction.
        alt_state_alts = map (\((Alt (dc, params), _), a_state) ->
                                  (Alt (dc, params), curr_expr a_state))
                             (zip as alt_states)
        -- Join them all together.
        slt' = joinSLTs $ [sym_links m_state] ++ (map sym_links alt_states)
        cexpr' = Case (curr_expr m_state) alt_state_alts t

        -- Function that allows us to express each Alt as a separate State
        -- that we can then later merge. We keep a list of previous States
        -- from folding so that we can use them to make conflict lists.
        altState :: [State] -> (Alt, Expr) -> [State]
        altState acc (Alt (dc, params), aexp) =
          let acc_alls = concatMap allNames acc  -- Super slow :)
              c_env = M.fromList $ zip acc_alls (repeat BAD)
              eenv' = M.union (expr_env state) c_env
              alt_st = state { expr_env = eenv', curr_expr = aexp }
          in if old `elem` params
              then acc ++ [alt_st]
              else acc ++ [rename old new alt_st]

-- | Rename Assume
renameAssume :: Name -> Name -> State -> State
renameAssume old new state = state_e {curr_expr = Assume c' e'}
  where Assume c e = curr_expr state
        state_c = rename old new (state {curr_expr = c})
        state_e = rename old new (state_c {curr_expr = e})
        c' = curr_expr state_c
        e' = curr_expr state_e

-- | Rename Assert
renameAssert :: Name -> Name -> State -> State
renameAssert old new state = state_e {curr_expr = Assert c' e'}
  where Assert c e = curr_expr state
        state_c = rename old new (state {curr_expr = c})
        state_e = rename old new (state_c {curr_expr = e})
        c' = curr_expr state_c
        e' = curr_expr state_e

--   Rename all variables of form (Var n) with (Var n'). We make the assumption
--   that the new name passed in is fresh with respect to the current state.
--   This allows us to prevent checking to see if the new name happens to equal
--   one of the names in a binder (cf Lam, Case, Let), and thus saves us the
--   effort of having to perform sub-expression renaming.
rename :: Name -> Name -> State -> State
rename old new state = case curr_expr state of
    Var _ _    -> renameVar    old new state
    Lam _ _ _  -> renameLam    old new state
    Let _ _    -> renameLet    old new state
    App _ _    -> renameApp    old new state
    Case _ _ _ -> renameCase   old new state
    Assume _ _ -> renameAssume old new state
    Assert _ _ -> renameAssert old new state
    otherwise  -> state

-- | Rename List
--   Rename, but with a list instead. If we pipe in the input from some fresh
--   seeded name list, we are guaranteed to have uniqueness at least, such that
--   the remaps don't step over on each other.
renameList :: [(Name, Name)] -> State -> State
renameList remaps state = foldl (\s (n, n') -> rename n n' s) state remaps

