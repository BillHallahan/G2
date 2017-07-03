-- | Renamer
--   Renaming is a hard problem, apparently. This is mainly because we assume
--   an arbitrary case where the names that appear in the expressions are NOT
--   all "fresh" -- that is, it is possible for lambda binders to have a
--   conflicting name with that of the current environment bindings. Thus, we
--   must be careful to avoid accidentally capturing free variables.

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Core.Renamer
    ( allNamesMap
    , allNames
    , freshSeededName
    , freshSeededNameList
    , renameExpr
    , renameExprList
    , renameType
    , renameTypeList) where

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

strip_seed :: Name -> Name
strip_seed = filter (not . C.isDigit)

-- | AllNamesMap
--   Returns all the names used in a state. We aggressively over approximate
--   because this function will mostly be used for conflict listing when making
--   fresh variable names -- hence it is safe to do so :)
allNamesMap :: State -> M.Map Name Int
allNamesMap s = foldr (\x m -> M.alter (maxMaybe x) (strip_seed x) m) M.empty $ allNames s
    where
        maxMaybe :: Name -> Maybe Int -> Maybe Int
        maxMaybe x (Just y) = Just (max (nameNum x) y)
        maxMaybe x Nothing = Just (nameNum x)

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
freshSeededName :: Name -> State -> (Name, State)
freshSeededName seed state = (fresh, state {all_names = M.insert stripped_seed new_num confs})
  where
        confs = all_names state
        -- max_confs_num = L.maximum $ [0] ++ (map nameNum confs)
        stripped_seed = strip_seed seed
        max_num = M.findWithDefault 0 stripped_seed confs
        new_num = max_num + 1
        fresh = stripped_seed ++ show (new_num)

-- | Fresh Seeded Name List
--   Given a list of seeds, generate a list of freshnames for them. We apply a
--   fold operation in order to keep track of a "history"
freshSeededNameList :: [Name] -> State -> ([Name], State)
freshSeededNameList [] s     = ([], s)
freshSeededNameList (n:ns) s = (n':ns', s'')
  where (n', s')   = freshSeededName n s
        (ns', s'') = freshSeededNameList ns s'

-- | Join Symbolic Link Tables
--   Can only safely join them if their new entries are disjoint!!
joinSLTs :: [SymLinkTable] -> SymLinkTable
joinSLTs slts = foldl M.union M.empty slts
 
-- | Rename Var
--   If it matches, we update, and add an entry to the symbolic link table.
renameExprVar :: Name -> Name -> State -> State
renameExprVar old new state = if n == old
    then state {curr_expr = cexpr', sym_links = slt'}
    else state
  where Var n t = curr_expr state
        slt'   = M.insert new (old, t, Nothing) (sym_links state) 
        cexpr' = Var new t

-- | Rename Lam
--   Must check for cases where the lambda's binder might be old or new.
renameExprLam :: Name -> Name -> State -> State
renameExprLam old new state = if b == old
    then state  -- Shadowing occurs
    else e_st {curr_expr = cexpr'}
  where Lam b e t = curr_expr state
        e_st   = renameExpr old new (state {curr_expr = e})
        cexpr' = Lam b (curr_expr e_st) t

-- | Rename Let
renameExprLet :: Name -> Name -> State -> State
renameExprLet old new state = if old `elem` bs_lhs
    then state  -- Shadowing occurs.
    else e_st {curr_expr = cexpr', sym_links = slt'}
  where Let bs e = curr_expr state
        bs_lhs = map fst bs
        bs_rhs = map snd bs
        e_st   = renameExpr old new (state {curr_expr = e})
        bs_sts = map (\(b, e) -> (b, renameExpr old new (state {curr_expr=e}))) bs
        bs'    = map (\(b, r_st) -> (b, curr_expr r_st)) bs_sts
        cexpr' = Let bs' (curr_expr e_st)
        slt'   = joinSLTs $ [sym_links e_st] ++ map (sym_links . snd) bs_sts

-- | Rename App
renameExprApp :: Name -> Name -> State -> State
renameExprApp old new state = a_st {curr_expr = cexpr'}
  where App f a = curr_expr state
        f_st = renameExpr old new (state {curr_expr = f})
        a_st = renameExpr old new (f_st {curr_expr = a})
        f' = curr_expr f_st
        a' = curr_expr a_st
        cexpr' = App f' a'

-- | Rename Alt
renameExprAltExp :: Name -> Name -> State -> (Alt, Expr) -> State
renameExprAltExp old new state (Alt (dc, params), aexp) = if old `elem` params
      then state {curr_expr = aexp}
      else renameExpr old new (state {curr_expr = aexp})

-- | Rename Case
--   Renaming occurs depending on if old shows up in the params.
renameExprCase :: Name -> Name -> State -> State
renameExprCase old new state = state {curr_expr = cexpr', sym_links = slt'}
  where Case m as t = curr_expr state
        m_st   = renameExpr old new (state {curr_expr = m})
        a_sts  = map (renameExprAltExp old new state) as
        as'    = map (\((Alt (dc, params), _), a_st) ->
                         (Alt (dc, params), curr_expr a_st))
                     (zip as a_sts)
        cexpr' = Case (curr_expr m_st) as' t
        slt'   = joinSLTs $ [sym_links m_st] ++ (map sym_links a_sts)

-- | Rename Assume
renameExprAssume :: Name -> Name -> State -> State
renameExprAssume old new state = e_st {curr_expr = cexpr'}
  where Assume c e = curr_expr state
        c_st = renameExpr old new (state {curr_expr = c})
        e_st = renameExpr old new (c_st {curr_expr = e})
        c' = curr_expr c_st
        e' = curr_expr e_st
        cexpr' = Assume c' e'

-- | Rename Assert
renameExprAssert :: Name -> Name -> State -> State
renameExprAssert old new state = e_st {curr_expr = cexpr'}
  where Assert c e = curr_expr state
        c_st = renameExpr old new (state {curr_expr = c})
        e_st = renameExpr old new (c_st {curr_expr = e})
        c' = curr_expr c_st
        e' = curr_expr e_st
        cexpr' = Assert c' e'

-- | Rename
--   Rename all variables of form (Var n) to (Var n'). We make an (aggressive)
--   assumption that the `new` passed in is fresh with respect to the current
--   state. This allows us to prevent checking to see if the new name happens
--   to equal one of the names in a binder (cf Lam, Case, Let), and thus saves
--   us the effort of having to perform sub-expression renaming.
renameExpr :: Name -> Name -> State -> State
renameExpr old new state = case curr_expr state of
    Var _ _    -> renameExprVar    old new state
    Lam _ _ _  -> renameExprLam    old new state
    Let _ _    -> renameExprLet    old new state
    App _ _    -> renameExprApp    old new state
    Case _ _ _ -> renameExprCase   old new state
    Assume _ _ -> renameExprAssume old new state
    Assert _ _ -> renameExprAssert old new state
    otherwise  -> state

-- | Rename List
--   Rename, but with a list instead. If we pipe in the input from some fresh
--   seeded name list, we are guaranteed to have uniqueness at least, such that
--   the remaps don't step over on each other.
renameExprList :: [(Name, Name)] -> State -> State
renameExprList [] state = state
renameExprList ((o, n):rs) state = renameExprList rs state'
  where state' = renameExpr o n state

-- | Rename TyVar
renameTyVar :: Name -> Name -> Type -> Type
renameTyVar old new (TyVar n) = if old == n then TyVar new else TyVar n

-- | Rename TyFun
renameTyFun :: Name -> Name -> Type -> Type
renameTyFun old new (TyFun t1 t2) = TyFun t1' t2'
  where t1' = renameType old new t1
        t2' = renameType old new t2

-- | Rename TyApp
renameTyApp :: Name -> Name -> Type -> Type
renameTyApp old new (TyApp t1 t2) = TyApp t1' t2'
  where t1' = renameType old new t1
        t2' = renameType old new t2

-- | Rename TyConApp Name [Type]
renameTyConApp :: Name -> Name -> Type -> Type
renameTyConApp old new (TyConApp n tys) = TyConApp n' tys'
  where n'   = if old == new then new else n
        tys' = map (renameType old new) tys

-- | Rename TyAlg
renameTyAlg :: Name -> Name -> Type -> Type
renameTyAlg old new (TyAlg n dcs) = TyAlg n' dcs'
  where n'   = if old == new then new else n
        dcs' = map (renameDataCon old new) dcs

-- | Rename TyForAll
renameTyForAll :: Name -> Name -> Type -> Type
renameTyForAll old new (TyForAll n t) = TyForAll n' t'
  where n' = if old == new then new else n
        t' = renameType old new t

-- | Rename Type
renameType :: (ASTContainer m Type) => Name -> Name -> m -> m
renameType old new = modifyASTs (renameType' old new)
    where
        renameType' :: Name -> Name -> Type -> Type
        renameType' old new ty = case ty of
            TyVar _      -> renameTyVar old new ty
            TyFun _ _    -> renameTyFun old new ty
            TyApp _ _    -> renameTyApp old new ty
            TyConApp _ _ -> renameTyConApp old new ty
            TyAlg _ _    -> renameTyAlg old new ty
            TyForAll _ _ -> renameTyForAll old new ty
            TyBottom     -> TyBottom

-- | Rename Type List
renameTypeList :: [(Name, Name)] -> Type -> Type
renameTypeList [] ty = ty
renameTypeList ((o, n):rs) ty = renameTypeList rs ty'
  where ty' = renameType o n ty

-- | Rename Data Constructor
renameDataCon :: Name -> Name -> DataCon -> DataCon
renameDataCon old new (DataCon n i ty tys) = DataCon n' i ty' tys'
  where n'   = if old == new then new else n
        ty'  = renameType old new ty
        tys' = map (renameType old new) tys


