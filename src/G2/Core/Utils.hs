-- | Utils
--   One basic rule of thumb when using this module is that all operations that
--   perform mutation should be passed a State so that we can make the
--   responsibility of correctness fall onto this module. However, if some
--   function's job is to merely extract information on some Core.Language,
--   then it is fine to have that function not use the bulky structure of a
--   State. The idea is that code in this module should be hard to use wrong.
--
--   In general, transformations and mutations are defined as operations such
--   as environment binding, and renaming, which produce an altered version of
--   one of the inputs that was passed in.
module G2.Core.Utils where

import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map  as M

import G2.Core.Language

-- | Expression Lookup
--   Did we find???
lookupExpr :: Name -> EEnv -> Maybe Expr
lookupExpr = M.lookup

-- | Type Lookup
--   ???
lookupType :: Name -> TEnv -> Maybe Type
lookupType = M.lookup

-- | Expression Binding
--   Bind a (Name, Expr) pair into the expression environment of a state.
bindExpr :: Name -> Expr -> State -> State
bindExpr name expr state = state {expr_env = eenv'}
  where eenv' = M.insert name expr (expr_env state)

-- | Expression Binding List
--   Bind a whole list of them.
bindExprList :: [(Name, Expr)] -> State -> State
bindExprList binds state = foldl (\s (n, e) -> bindExpr n e s) state binds

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
        dcs (DataCon dcn _ t ps) = [dcn] ++ tys t ++ concatMap tys ps
        dcs DEFAULT = []
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
        exs (Data dc) = dcs dc
        exs (Case m as t) = exs m ++ concatMap altxs as ++ tys t
        exs (Type t) = tys t
        exs (Spec c e) = exs c ++ exs e
        exs _ = []

-- | Fresh Name
--   Generates a fresh name given a state. Default seed is "f$".
freshName :: State -> Name
freshName = freshSeededName "f$"

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
freshSeededNameList (n:ns) s =
    let
        n' = freshSeededName n s
        s' = bindExpr n' BAD s  -- Conflict
    in
    n':freshSeededNameList ns s'

-- | Rename
--   Rename all variables of form (Var n) with (Var n').
rename :: Name -> Name -> State -> State
rename old new state = case curr_expr state of
  -- If it matches, we update, and add an entry to the symbolic link table.
  Var n t -> let sym_links' = M.insert new (old,t,Nothing) (sym_links state) 
             in if n == old
               then state { curr_expr = Var new t, sym_links = sym_links'}
               else state

  -- Must check for cases where the lambda's binder might be old or new.
  Lam b e t -> if old == b
                 -- We are unable to continue due to variable shadowing.
                 then state
                 else if new == b
                   -- We must change the binder to something else.
                   then let b' = freshSeededName b state  -- b' /= new
                            state' = rename b b' (state {curr_expr = e})
                            e' = curr_expr state'
                            sym_links' = sym_links state'
                        in rename old new (state' { curr_expr = Lam b' e' t
                                                  , sym_links = sym_links' })
                   -- Can safely proceed!
                   else let state' = rename old new (state {curr_expr = e})
                        in state { curr_expr = Lam b (curr_expr state') t
                                 , sym_links = sym_links state' }

  -- This is more straightforward than Lam. Branch and union the sym links.
  App f a -> let state_f = rename old new (state {curr_expr = f})
                 state_a = rename old new (state_f {curr_expr = a})
                 f' = curr_expr state_f
                 a' = curr_expr state_a
             in state_a {curr_expr = App f' a'}

  -- Hooooly fuck this is complicated.
  Case m as t ->
          -- Function that allows us to express each Alt as a separate State
          -- that we can then later merge. We keep a list of previous States
          -- from folding so that we can use them to make conflict lists.
      let altState :: [State] -> (Alt, Expr) -> [State]
          altState acc (Alt (dc, params), aexp) =
            let acc_alls = concatMap allNames acc  -- Super slow :)
                c_env = M.fromList $ zip acc_alls (repeat BAD)
                alt_st = state { expr_env = M.union (expr_env state) c_env
                               , curr_expr = aexp }
            in if old `elem` params
              -- We have achieved variable shadowing.
              then acc ++ [alt_st]
              else if new `elem` params
                -- We must rename the existing datacon params.
                then let params' = freshSeededNameList params alt_st
                         zipd = zip params params'
                         alt_st' = renameList zipd alt_st
                         aexp' = curr_expr alt_st'
                         slk' = sym_links alt_st'
                     in acc ++ [rename old new (alt_st' { curr_expr = aexp'
                                                        , sym_links = slk' })]
                -- Okay to rename!
                else acc ++ [rename old new alt_st]
          -- Fold over the slt's to join them. It is only safe to do so if we
          -- can guarantee some level of mutual exclusion in terms of the
          -- names added, hence why altState requires the previous states in
          -- order to make an effective conflict list.
          joinSLTs :: [SymLinkTable] -> SymLinkTable
          joinSLTs slts = foldl M.union M.empty slts
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
          slts = joinSLTs $ [sym_links m_state] ++ (map sym_links alt_states)
      in state { curr_expr = Case (curr_expr m_state) alt_state_alts t
               , sym_links = slts }

  -- Rename the LHS, then RHS. Similar to App.
  Spec cond exp -> let state_c = rename old new (state {curr_expr = cond})
                       state_e = rename old new (state_c {curr_expr = exp})
                       cond' = curr_expr state_c
                       exp'  = curr_expr state_e
                  in state_e {curr_expr = Spec cond' exp'}

  -- Everything else.
  _ -> state

-- | Rename List
--   Rename, but with a list instead. If we pipe in the input from some fresh
--   seeded name list, we are guaranteed to have uniqueness at least, such that
--   the remaps don't step over on each other.
renameList :: [(Name, Name)] -> State -> State
renameList remaps state = foldl (\s (n, n') -> rename n n' s) state remaps

-- | Expression Type
--   Gets the type of an expression.
exprType :: Expr -> Type
exprType (Var _ t) = t
exprType (Const (CInt _))    = TyRawInt
exprType (Const (CFloat _))  = TyRawFloat
exprType (Const (CDouble _)) = TyRawDouble
exprType (Const (CChar _))   = TyRawChar
exprType (Const (CString _)) = TyRawString
exprType (Const (COp _ t))   = t
exprType (Lam _ _ t) = t
exprType (App f a) = case exprType f of {TyFun l r->r; t->TyApp t (exprType a)}
exprType (Data (DataCon n _ t a)) = L.foldl1 (\b r->TyFun r b) (reverse a++[t])
exprType (Data DEFAULT) = TyBottom
exprType (Case _ _ t) = t
exprType (Type t) = t
exprType (Spec c e) = exprType e
exprType (BAD) = TyBottom

