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

-- | Expression Top-Level Names
exprTopNames :: Expr -> [Name]
exprTopNames (Var n t)     = [n]
exprTopNames (Const (COp n t)) = [n]
exprTopNames (Lam b e t)   = [b]
exprTopNames (Let bs e)    = map fst bs
exprTopNames (Case m as t) = concatMap (\(Alt (_, ps), _) -> ps) as
exprTopNames _ = []

-- | Type Top-Level Names
typeTopNames :: Type -> [Name]
typeTopNames (TyVar n)   = [n]
typeTopNames (TyConApp n _) = [n]
typeTopNames (TyAlg n _) = [n]
typeTopNames (TyForAll n _) = [n]
typeTopNames _ = []

-- | All Names
--   Returns all the names used in a state. We aggressively over approximate
--   because this function will mostly be used for conflict listing when making
--   fresh variable names -- hence it is safe to do so :)
allNames :: State -> [Name]
allNames state = L.nub (expr_names ++ type_names ++ eenv_keys ++ tenv_keys)
  where expr_names = evalASTs exprTopNames state
        type_names = evalASTs typeTopNames state
        eenv_keys = (M.keys . expr_env) state
        tenv_keys = (M.keys . type_env) state

-- | Name to Number
--   Highest number sequence in a name, ignoring characters.
nameNum :: Name -> Int
nameNum name = case filter C.isDigit name of
    [] -> 0
    xs -> read xs :: Int

-- | Fresh Seeded Name
--   We want this new name to be different from all other names in the state.   
freshSeededName :: Name -> State -> Name
freshSeededName seed state = stripped_seed ++ show (max_confs_num + 1)
  where conflicts = allNames state
        max_confs_num = L.maximum $ [0] ++ (map nameNum conflicts)
        stripped_seed = filter (not . C.isDigit) seed

-- | Fresh Seeded Name List
--   Given a list of seeds, generate a list of freshnames for them. We apply a
--   fold operation in order to keep track of a "history".
freshSeededNameList :: [Name] -> State -> [Name]
freshSeededNameList [] _ = []
freshSeededNameList (n:ns) s = [n'] ++ freshSeededNameList ns s'
  where n' = freshSeededName n s
        s' = bindExpr n' BAD s  -- Conflict

-- | Join Symbolic Link Tables
--   Can only safely join them if their new entries are disjoint!!
joinSLTs :: [SymLinkTable] -> SymLinkTable
joinSLTs slts = foldl M.union M.empty slts
 
-- | Rename Var
--   If it matches, we update, and add an entry to the symbolic link table.
renameVar :: Name -> Name -> State -> State
renameVar old new state = if n == old
    then state {curr_expr = cexpr', sym_links = slt'}
    else state
  where Var n t = curr_expr state
        slt'   = M.insert new (old, t, Nothing) (sym_links state) 
        cexpr' = Var new t

-- | Rename Lam
--   Must check for cases where the lambda's binder might be old or new.
renameLam :: Name -> Name -> State -> State
renameLam old new state = if b == old
    then state  -- Shadowing occurs
    else e_st {curr_expr = cexpr'}
  where Lam b e t = curr_expr state
        e_st   = rename old new (state {curr_expr = e})
        cexpr' = Lam b (curr_expr e_st) t

-- | Rename Let
renameLet :: Name -> Name -> State -> State
renameLet old new state = if old `elem` bs_lhs
    then state  -- Shadowing occurs.
    else e_st {curr_expr = cexpr', sym_links = slt'}
  where Let bs e = curr_expr state
        bs_lhs = map fst bs
        bs_rhs = map snd bs
        e_st   = rename old new (state {curr_expr = e})
        bs_sts = map (\(b, e) -> (b, rename old new (state {curr_expr=e}))) bs
        bs'    = map (\(b, r_st) -> (b, curr_expr r_st)) bs_sts
        cexpr' = Let bs' (curr_expr e_st)
        slt'   = joinSLTs $ [sym_links e_st] ++ map (sym_links . snd) bs_sts

-- | Rename App
renameApp :: Name -> Name -> State -> State
renameApp old new state = a_st {curr_expr = cexpr'}
  where App f a = curr_expr state
        f_st = rename old new (state {curr_expr = f})
        a_st = rename old new (f_st {curr_expr = a})
        f' = curr_expr f_st
        a' = curr_expr a_st
        cexpr' = App f' a'

-- | Rename Alt
renameAltExp :: Name -> Name -> State -> (Alt, Expr) -> State
renameAltExp old new state (Alt (dc, params), aexp) = if old `elem` params
      then state {curr_expr = aexp}
      else rename old new (state {curr_expr = aexp})

-- | Rename Case
--   Renaming occurs depending on if old shows up in the params.
renameCase :: Name -> Name -> State -> State
renameCase old new state = state {curr_expr = cexpr', sym_links = slt'}
  where Case m as t = curr_expr state
        m_st   = rename old new (state {curr_expr = m})
        a_sts  = map (renameAltExp old new state) as
        as'    = map (\((Alt (dc, params), _), a_st) ->
                         (Alt (dc, params), curr_expr a_st))
                     (zip as a_sts)
        cexpr' = Case (curr_expr m_st) as' t
        slt'   = joinSLTs $ [sym_links m_st] ++ (map sym_links a_sts)

-- | Rename Assume
renameAssume :: Name -> Name -> State -> State
renameAssume old new state = e_st {curr_expr = cexpr'}
  where Assume c e = curr_expr state
        c_st = rename old new (state {curr_expr = c})
        e_st = rename old new (c_st {curr_expr = e})
        c' = curr_expr c_st
        e' = curr_expr e_st
        cexpr' = Assume c' e'

-- | Rename Assert
renameAssert :: Name -> Name -> State -> State
renameAssert old new state = e_st {curr_expr = cexpr'}
  where Assert c e = curr_expr state
        c_st = rename old new (state {curr_expr = c})
        e_st = rename old new (c_st {curr_expr = e})
        c' = curr_expr c_st
        e' = curr_expr e_st
        cexpr' = Assert c' e'

-- | Rename
--   Rename all variables of form (Var n) to (Var n'). We make an (aggressive)
--   assumption that the `new` passed in is fresh with respect to the current
--   state. This allows us to prevent checking to see if the new name happens
--   to equal one of the names in a binder (cf Lam, Case, Let), and thus saves
--   us the effort of having to perform sub-expression renaming.
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

