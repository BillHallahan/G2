{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.Merging.StateMerging
  ( mergeState
  -- , mergeCurrExpr
  -- , mergeExpr
  -- , mergeExprEnv
  -- , mergeEnvObj
  -- , mergePathConds
  -- , emptyContext
  -- , Context
  , createCaseExpr
  , concretizeSym
  , bindExprToNum
  , implies
  , restrictSymVal
  ) where

import G2.Language
import G2.Execution.NormalForms
import G2.Solver.Simplifier
import qualified G2.Language.ExprEnv as E 
import qualified G2.Language.PathConds as PC

import Control.Exception
import qualified Control.Monad.State.Lazy as S
import Data.Maybe
import qualified Data.List as L
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M

import Debug.Trace

isMergeable :: Eq t => State t -> State t -> Bool
isMergeable s1 s2 = 
    (exec_stack s1 == exec_stack s2)
    && (isMergeableCurrExpr (expr_env s1) (expr_env s2) (curr_expr s1) (curr_expr s2))
    && (type_env s1 == type_env s2)
    && (known_values s1 == known_values s2)
    && (non_red_path_conds s1 == non_red_path_conds s2)
    && (true_assert s1 == true_assert s2)
    && (assert_ids s1 == assert_ids s2)
    && (tags s1 == tags s2)
    && (track s1 == track s2)
    && (type_classes s1 == type_classes s2)
    -- && (cases s1) == (cases s2)
    && (isEmpty $ model s1)
    && (isEmpty $ model s2)

isMergeableCurrExpr :: E.ExprEnv -> E.ExprEnv -> CurrExpr -> CurrExpr -> Bool
isMergeableCurrExpr eenv1 eenv2 (CurrExpr Evaluate ce1) (CurrExpr Evaluate ce2) = isMergeableExpr eenv1 eenv2 ce1 ce2
isMergeableCurrExpr eenv1 eenv2 (CurrExpr Return ce1) (CurrExpr Return ce2) = isMergeableExpr eenv1 eenv2 ce1 ce2
isMergeableCurrExpr _ _ _ _ = False

-- | Returns True if both Exprs are of the form (App ... (App (Data DataCon)) ....) or (App ... (App (Var x)) ...), where (Var x) is a Symbolic variable
isMergeableExpr :: E.ExprEnv -> E.ExprEnv -> Expr -> Expr -> Bool
isMergeableExpr eenv1 eenv2 (App e1 _) (App e1' _) = isMergeableExpr eenv1 eenv2 e1 e1'
isMergeableExpr _ _ (Data dc1) (Data dc2) = dc1 == dc2
-- isMergeableExpr eenv1 eenv2 (Var i1) (Var i2)
--     | (Just (E.Sym _)) <- E.lookupConcOrSym (idName i1) eenv1
--     , (Just (E.Sym _)) <- E.lookupConcOrSym (idName i2) eenv2
--     , typeOf i1 == typeOf i2 = True
isMergeableExpr _ _ _ _ = True
-- (allowing all exprs in SMNF - i.e. Case Exprs, to be merged yields no performance improvement)

type MergeId = Id

-- | Values that are passed around and updated while merging individual fields in 2 States
data Context t = Context { renamed1_ :: HM.HashMap Name Name -- Map from old Names in State `s1_` to new Names
                         , renamed2_ :: HM.HashMap Name Name
                         , s1_ :: State t
                         , s2_ :: State t
                         , ng_ :: NameGen
                         , newId_ :: MergeId -- `newId` is set to 1 or 2 in an AssumePC/ Case Expr when merging values from `s1_` or `s2_` respectively
                         , newPCs_ :: [PathCond]
                         , newSyms_ :: SymbolicIds -- Newly added symbolic variables when merging Exprs
                         }

type MergedIds = HM.HashMap (Name, Name) Id

emptyContext :: State t -> State t -> NameGen -> Id -> Context t
emptyContext s1 s2 ng newId = Context { renamed1_ = HM.empty
                                      , renamed2_ = HM.empty
                                      , s1_ = s1
                                      , s2_ = s2
                                      , ng_ = ng
                                      , newId_ = newId
                                      , newPCs_ = []
                                      , newSyms_ = HS.empty}

mergeState :: (Eq t, Named t, Simplifier simplifier) => NameGen -> simplifier -> State t -> State t -> (NameGen, Maybe (State t))
mergeState ngen simplifier s1 s2 =
    if isMergeable s1 s2
        then 
            let (newId, ngen') = freshMergeId TyLitInt ngen
                ctxt = emptyContext s1 s2 ngen' newId
                (curr_expr', m_ns, ctxt') = newMergeCurrExprCxt ctxt
                -- m_ns = HM.empty
                -- (ctxt', curr_expr') = mergeCurrExpr ctxt
                (eenv', ctxt'') = newMergeExprEnvCxt ctxt' m_ns
                -- (ctxt'', eenv') = mergeExprEnv ctxt'
                (ctxt''', path_conds') = mergePathConds simplifier ctxt''
                syms' = mergeSymbolicIds ctxt'''
                s1' = s1_ ctxt'''
                ngen'' = ng_ ctxt'''
            in
            (ngen''
               , (Just State { expr_env = eenv'
                             , type_env = type_env s1'
                             , curr_expr = curr_expr'
                             , path_conds = path_conds'
                             , non_red_path_conds = non_red_path_conds s1'
                             , true_assert = true_assert s1'
                             , assert_ids = assert_ids s1'
                             , type_classes = type_classes s1'
                             , symbolic_ids = syms'
                             , exec_stack = exec_stack s1'
                             , model = model s1'
                             , known_values = known_values s1'
                             , cases = cases s1' -- both should be equal
                             , ready_to_merge = ready_to_merge s1'
                             , rules = rules s1'
                             , num_steps = max (num_steps s1) (num_steps s2)
                             , track = track s1'
                             , tags = tags s1' }))
        else (ngen, Nothing)

newMergeCurrExprCxt :: Context t -> (CurrExpr, MergedIds, Context t)
newMergeCurrExprCxt cxt@(Context { s1_ = s1, s2_ = s2, newPCs_ = pc, ng_ = ng, newId_ = m_id }) =
    let
        (ce', m_ns, eenv', pc', symbs1, symbs2, ng') =
            newMergeCurrExpr (expr_env s1) (expr_env s2) (type_env s1)
                             (known_values s1)
                             ng
                             (symbolic_ids s1) (symbolic_ids s2)
                              m_id (curr_expr s1) (curr_expr s2)

        eenv1 = E.union eenv'
              $ foldr (\i -> E.insertSymbolic (idName i) i) (expr_env s1) symbs1
        eenv2 = E.union eenv'
              $ foldr (\i -> E.insertSymbolic (idName i) i) (expr_env s2) symbs2
    in
    (ce', m_ns, cxt { s1_ = s1 { expr_env = eenv1
                               , symbolic_ids = symbs1 }
                    , s2_ = s2 { expr_env = eenv2
                               , symbolic_ids = symbs2 }
                    , newPCs_ = pc ++ pc'
                    , ng_ = ng' } )

newMergeCurrExpr :: ExprEnv
                 -> ExprEnv
                 -> TypeEnv
                 -> KnownValues
                 -> NameGen
                 -> SymbolicIds
                 -> SymbolicIds
                 -> MergeId
                 -> CurrExpr
                 -> CurrExpr
                 -> (CurrExpr, MergedIds, ExprEnv, [PathCond], SymbolicIds, SymbolicIds, NameGen)
newMergeCurrExpr eenv1 eenv2 tenv kv ng symbs1 symbs2 m_id (CurrExpr er1 e1) (CurrExpr er2 e2)
    | er1 == er2 =
        let
            (m_e, m_ns', eenv', pc', symb1', symb2', ng') = newMergeCurrExpr' eenv1 eenv2 tenv kv ng symbs1 symbs2 m_id e1 e2
        in
        (CurrExpr er1 m_e, m_ns', eenv', pc', symb1', symb2', ng')
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."

newMergeCurrExpr' :: ExprEnv
                  -> ExprEnv
                  -> TypeEnv
                  -> KnownValues
                  -> NameGen
                  -> SymbolicIds
                  -> SymbolicIds
                  -> MergeId
                  -> Expr
                  -> Expr
                  -> (Expr, MergedIds, ExprEnv, [PathCond], SymbolicIds, SymbolicIds, NameGen)
newMergeCurrExpr' eenv1 eenv2 tenv kv ng symbs1 symbs2 m_id e1 e2 =
    let
        (eenv, e1', pc1, symbs1', ng') = 
            case e1 of
                Var i@(Id n t)
                    | E.isSymbolic n eenv1 ->
                        let
                            (e_, pc_, symbs_, ng_) = arbDCCase tenv ng t
                        in
                        (E.singleton n e_, e_, pc_, HS.union symbs_ $ HS.delete i symbs1, ng_)
                _ -> (E.empty, e1, [], symbs1, ng)

        (eenv', e2', pc2, symbs2', ng'') = 
            case e2 of
                Var i@(Id n t)
                    | E.isSymbolic n eenv2 ->
                        let
                            (e_, pc_, symbs_, ng_) = arbDCCase tenv ng' t
                        in
                        (E.insert n e_ eenv, e_, pc_, HS.union symbs_ $ HS.delete i symbs2, ng_)
                _ -> (eenv, e2, [], symbs2, ng')

        (m_e, m_ns, pc, symbs, ng''') = newMergeExpr kv ng'' m_id HM.empty eenv1 eenv2 e1' e2'
    in
    ( m_e
    , m_ns
    , eenv'
    , pc1 ++ pc2 ++ pc
    , symbs1' `HS.union` symbs
    , symbs2' `HS.union` symbs
    , ng''')

mergeCurrExpr :: Named t => Context t -> (Context t, CurrExpr)
mergeCurrExpr ctxt@(Context { s1_ = (State {curr_expr = ce1}), s2_ = (State {curr_expr = ce2}) })
    | (CurrExpr evalOrRet1 e1) <- ce1
    , (CurrExpr evalOrRet2 e2) <- ce2
    , evalOrRet1 == evalOrRet2 =
        let (ctxt', e1', e2') = inlineExpr ctxt HS.empty HS.empty e1 e2
            (ctxt'', ce) = mergeInlinedExpr ctxt' e1' e2'
        in
        (ctxt'', CurrExpr evalOrRet1 ce)
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."


------------------------------------------------
-- Merging expressions

type NewSymbolicIds = SymbolicIds

newMergeExprEnvCxt :: Context t -> MergedIds -> (ExprEnv, Context t)
newMergeExprEnvCxt cxt@(Context { s1_ = s1, s2_ = s2, newPCs_ = pc, ng_ = ng, newId_ = m_id }) m_ns =
    let
        (eenv', pc', symbs', ng') =
            newMergeExprEnv (known_values s1) ng m_id m_ns (symbolic_ids s1) (symbolic_ids s2) (type_env s1) (expr_env s1) (expr_env s2)
    in
    (eenv', cxt { s1_ = s1 { symbolic_ids = symbs'}
                , s2_ = s2 { symbolic_ids = symbs' }
                , newPCs_ = pc ++ pc'
                , ng_ = ng' } )

newMergeExprEnv :: KnownValues
                -> NameGen
                -> MergeId
                -> MergedIds
                -> SymbolicIds
                -> SymbolicIds
                -> TypeEnv
                -> ExprEnv
                -> ExprEnv
                -> (ExprEnv, [PathCond], SymbolicIds, NameGen)
newMergeExprEnv kv ng m_id m_ns symb1 symb2 tenv eenv1 eenv2 =
    let 
        (n_eenv, (m_ns', n_pc, symbs, n_symb, ng')) = 
            S.runState (E.mergeAEnvObj
                        E.preserveMissing
                        E.preserveMissing
                        (E.zipWithAMatched (newMergeEnvObj kv m_id tenv eenv1 eenv2)) 
                        eenv1 
                        eenv2)
                        (m_ns, [], symb1 `HS.union` symb2, HS.empty, ng)

        n_eenv' = foldr (\i -> E.insertSymbolic (idName i) i) n_eenv n_symb

        (n_eenv'', n_pc', symbs', ng'') = resolveNewVariables tenv kv ng' m_id (HM.union m_ns m_ns') symbs eenv1 eenv2 n_eenv'

        n_eenv''' = foldr (\i -> E.insertSymbolic (idName i) i) n_eenv'' symbs'

    in
    (n_eenv''', n_pc ++ n_pc', symbs', ng'')

newMergeEnvObj :: KnownValues -> Id -> TypeEnv -> ExprEnv -> ExprEnv -> Name -> E.EnvObj -> E.EnvObj
               -> S.State (MergedIds, [PathCond], SymbolicIds, NewSymbolicIds, NameGen) E.EnvObj
newMergeEnvObj kv m_id tenv eenv1 eenv2 n eObj1 eObj2
    | E.EqFast eObj1 == E.EqFast eObj2 = return eObj1
    | E.ExprObj _ e1 <- eObj1
    , E.ExprObj _ e2 <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (m_e, m_ns', pc', symb', ng') = newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1 e2
        S.put (HM.union m_ns m_ns', pc ++ pc', HS.union symb symb', HS.union symb' n_symb, ng')
        return $ E.ExprObj Nothing m_e
    -- Replace the Id in the SymbObj with a new Symbolic Id and merge with the expr from the ExprObj in a Case expr.
    -- If the Id is symbolic in one expression and concrete in the other, it must be an ADT.
    -- ADT Ids never appear in PathConds, so we do not need to worry about updating the PathConds.
    | (E.SymbObj i) <- eObj1
    , (E.ExprObj _ e2) <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (e_s, pc', f_symb', ng') = arbDCCase tenv ng (typeOf i)
        let (e, m_ns', pc'', symb', ng'') = newMergeExpr kv ng' m_id m_ns eenv1 eenv2 e_s e2
        S.put ( HM.union m_ns m_ns'
              , pc ++ pc' ++ pc''
              , HS.union symb' . HS.union f_symb' $ HS.delete i symb
              , HS.union symb' $ HS.union f_symb' n_symb
              , ng'')
        return $ E.ExprObj Nothing e
    | (E.ExprObj _ e1) <- eObj1
    , (E.SymbObj i) <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (e_s, pc', f_symb', ng') = arbDCCase tenv ng (typeOf i)
        let (e, m_ns', pc'', symb', ng'') = newMergeExpr kv ng' m_id m_ns eenv1 eenv2 e1 e_s
        S.put ( HM.union m_ns m_ns'
              , pc ++ pc' ++ pc''
              , HS.union symb' . HS.union f_symb' $ HS.delete i symb
              , HS.union symb' $ HS.union f_symb' n_symb
              , ng'')
        return $ E.ExprObj Nothing e
    -- Create a Case Expr combining the lookup Var with the expr from the ExprObj
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj _ e2) <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (e, m_ns', pc', symb', ng') = newMergeExpr kv ng m_id m_ns eenv1 eenv2 (Var $ nameToId n eenv1) e2
        S.put (HM.union m_ns m_ns', pc ++ pc', HS.union symb symb', n_symb, ng')
        return $ E.ExprObj Nothing e
    | (E.ExprObj _ e1) <- eObj1
    , (E.RedirObj n) <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (e, m_ns', pc', symb', ng') = newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1 (Var $ nameToId n eenv2)
        S.put (HM.union m_ns m_ns', pc ++ pc', HS.union symb symb', n_symb, ng')
        return $ E.ExprObj Nothing e
    | (E.RedirObj n1) <- eObj1
    , (E.RedirObj n2) <- eObj2 = do
        (m_ns, pc, symb, n_symb, ng) <- S.get
        let (e, m_ns', pc', symb', ng') =
              newMergeExpr kv ng m_id m_ns eenv1 eenv2 (Var $ nameToId n1 eenv1) (Var $ nameToId n2 eenv2)
        S.put (HM.union m_ns m_ns', pc ++ pc', HS.union symb symb', n_symb, ng')
        return $ E.ExprObj Nothing e
    | (E.SymbObj i1) <- eObj1
    , (E.SymbObj i2) <- eObj2
    , i1 == i2 = return eObj1
    | otherwise = error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

-- | Build a case expression with one alt for each data constructor of the given type
-- and symbolic arguments.  Thus, the case expression could evaluate to any value of the
-- given type.
arbDCCase :: TypeEnv
          -> NameGen
          -> Type
          -> (Expr, [PathCond], HS.HashSet Id, NameGen)
arbDCCase tenv ng t
    | TyCon tn _:ts <- unTyApp t
    , Just adt <- M.lookup tn tenv =
        let
            dcs = dataCon adt
            (bindee_id, ng') = freshId TyLitInt ng

            bound = boundIds adt
            bound_ts = zip bound ts

            ty_apped_dcs = map (\dc -> mkApp $ Data dc:map Type ts) dcs
            ((ng'', symbs), apped_dcs) =
                        L.mapAccumL
                            (\(ng_, symbs_) dc ->
                                let
                                    anon_ts = anonArgumentTypes dc
                                    re_anon = foldr (\(i, t) -> retype i t) anon_ts bound_ts
                                    (ars, ng_') = freshIds re_anon ng_
                                    symbs_' = foldr HS.insert symbs_ ars
                                in
                                ((ng_', symbs_'), mkApp $ dc:map Var ars)
                            )
                            (ng', HS.empty)
                            ty_apped_dcs

            bindee = Var bindee_id

            pc = mkBounds bindee 1 (toInteger $ length dcs)

            e = createCaseExpr bindee_id apped_dcs
        in
        (e, pc, HS.insert bindee_id symbs, ng'')
    | otherwise = error "arbDCCase: type not found"

nameToId :: Name -> ExprEnv -> Id
nameToId n eenv
    | Just e <- E.lookup n eenv = Id n (typeOf e)
    | otherwise = error "nameToId: name not found"

-- Takes two expressions to merge.  In addition, takes a map from pairs of
-- variables names to a single name, which can be substituted in place of
-- the variables.
-- Returns the results of merging the expressions, as well as a HashMap of
-- new name pairs which must be merged.
newMergeExpr :: KnownValues
             -> NameGen
             -> MergeId
             -> MergedIds
             -> ExprEnv
             -> ExprEnv
             -> Expr
             -> Expr
             -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
newMergeExpr _ ng m_id m_ns eenv1 eenv2 v@(Var (Id n1 t)) (Var (Id n2 _))
    | n1 == n2 = (v, HM.empty, [], HS.empty, ng)
    | Just i <- HM.lookup (n1, n2) m_ns = (Var i, HM.empty, [], HS.empty, ng)
    | otherwise =
        let
            (i, ng') = freshId t ng
        in
        (Var i, HM.singleton (n1, n2) i, [], HS.empty, ng')
-- newMergeExpr kv ng m_id m_ns a1@(App e1 e2) a2@(App e1' e2')
--     | typeOf e1 .::. typeOf e1' && typeOf e2 .::. typeOf e2' =
--         let
--             (n_e1, m_ns1, pc1, symb1, ng') = newMergeExpr kv ng m_id m_ns e1 e1'
--             (n_e2, m_ns2, pc2, symb2, ng'') = newMergeExpr kv ng' m_id (HM.union m_ns m_ns1) e2 e2'
--         in
--         (App n_e1 n_e2, HM.union m_ns1 m_ns2, pc1 ++ pc2, symb1 `HS.union` symb2, ng'')
newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1 e2
    | d@(Data (DataCon n1 _)):es1 <- unApp e1
    , Data (DataCon n2 _):es2 <- unApp e2 
    , n1 == n2 =
    let
        ((m_ns', pc', symbs', ng'), es) =
            L.mapAccumL
                (\(m_ns_, pc_, symbs_, ng_) (e1, e2) ->
                    let
                        (e, m_ns_', pc_', symbs_', ng_') = newMergeExpr kv ng_ m_id (HM.union m_ns m_ns_) eenv1 eenv2 e1 e2
                    in
                    ((m_ns_ `HM.union` m_ns_', pc_ ++ pc_', symbs_ `HS.union` symbs_', ng_'), e)
                )
                (HM.empty, [], HS.empty, ng) $ zip es1 es2
    in
    (mkApp $ d:es, m_ns', pc', symbs', ng')
newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1 e2@(Case (Var i2) b2 as2)
    | Data dc1:_ <- unApp e1
    , isSMNFCase e2 = newMergeDataConCase kv ng eenv1 eenv2 m_id m_ns dc1 1 e1 i2 as2
newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1@(Case (Var i1) b1 as1) e2
    | Data dc2:_ <- unApp e2
    , isSMNFCase e1 = newMergeDataConCase kv ng eenv1 eenv2 m_id m_ns dc2 2 e2 i1 as1
newMergeExpr kv ng m_id m_ns eenv1 eenv2 e1@(Case (Var i1) b1 as1) e2@(Case (Var i2) b2 as2) 
    | isSMNFCase e1
    , isSMNFCase e2 = newMergeCaseExprs kv ng eenv1 eenv2 m_id m_ns i1 as1 i2 as2
newMergeExpr _ ng _ _ _ _ ty@(Type t) (Type t') = assert (t == t') (ty, HM.empty, [], HS.empty, ng)
newMergeExpr _ ng m_id _ _ _ e1 e2 = 
    let
        (e, pc, i, ng') = newCaseExpr ng m_id e1 e2
    in
    (e, HM.empty, pc, HS.singleton i, ng')

newMergeExprs :: KnownValues
              -> NameGen
              -> ExprEnv
              -> ExprEnv
              -> MergeId
              -> MergedIds
              -> [Expr]
              -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
newMergeExprs kv ng eenv1 eenv2 m_id m_ns (e:es) =
    foldr (\e2 (e1, m_ns_, pc_, symbs_, ng_) ->
              let
                  (n_e, n_m_ns, n_pc, n_symbs, n_ng) = newMergeExpr kv ng_ m_id (m_ns `HM.union` m_ns_) eenv1 eenv2 e1 e2
              in
              (n_e, m_ns_ `HM.union` n_m_ns, pc_ ++ n_pc, symbs_ `HS.union` n_symbs, n_ng))
          (e, HM.empty, [], HS.empty, ng)
          es
newMergeExprs _ _ _ _ _ _ _ = error  "newMergeExprs: empty list"

newCaseExpr :: NameGen -> MergeId -> Expr -> Expr -> (Expr, [PathCond], Id, NameGen)
newCaseExpr ng m_id e1 e2 =
    let
        (binder, ng') = freshId TyLitInt ng
    in
    (Case (Var m_id) binder [ Alt (LitAlt $ LitInt 1) e1
                            , Alt (LitAlt $ LitInt 2) e2 ]
    , mkBounds (Var m_id) 1 2
    , binder
    , ng')

mkBounds :: Expr -> Integer -> Integer -> [PathCond]
mkBounds e l u =
    let
        t = TyFun TyLitInt $ TyFun TyLitInt TyLitInt
    in
    [ ExtCond (App (App (Prim Le t) (Lit (LitInt l))) e) True
    , ExtCond (App (App (Prim Le t) e) (Lit (LitInt u))) True]


-- newMergeDataCons :: KnownValues
--                  -> NameGen
--                  -> MergeId
--                  -> MergedIds
--                  -> DataCon
--                  -> Integer -- ^ What integer value is required of the merge id?
--                  -> Expr
--                  -> DataCon
--                  -> Integer -- ^ What integer value is required of the merge id?
--                  -> Expr
--                  -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
-- newMergeDataCons kv ng m_id m_ns dc1 i1 e1 dc2 i2 e2
--     | dc1 == dc2 = 
--     -- let
--     --     as_info1 = (dc1, m_id, i1, e1)
--     --     as_info2 = (dc2, m_id, i2, e2)
--     -- in
--     -- newMergeIntoCase kv ng m_id m_ns $ trace ("as_info1 = " ++ show as_info1 ++ "\nas_info2 = " ++ show as_info2) [as_info1, as_info2]

newMergeDataConCase :: KnownValues
                    -> NameGen
                    -> ExprEnv
                    -> ExprEnv
                    -> MergeId
                    -> MergedIds
                    -> DataCon
                    -> Integer -- ^ What integer value is required of the merge id?
                    -> Expr
                    -> Id -- ^ Case 2 bindee variable id
                    -> [Alt] -- ^ Case 2 Alts (with constructors in SMNF)
                    -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
newMergeDataConCase kv ng eenv1 eenv2 m_id m_ns dc i e bind2 as2 =
    let
        as_info1 = (dc, m_id, i, e)
        as_info2 = map (smnfAltInfo bind2) as2
    in
    newMergeIntoCase kv ng eenv1 eenv2 m_id m_ns $ as_info1:as_info2


newMergeCaseExprs :: KnownValues
                  -> NameGen
                  -> ExprEnv
                  -> ExprEnv
                  -> MergeId
                  -> MergedIds
                  -> Id -- ^ Case 1 bindee variable id
                  -> [Alt] -- ^ Case 1 Alts (with constructors in SMNF)
                  -> Id -- ^ Case 2 bindee variable id
                  -> [Alt] -- ^ Case 2 Alts (with constructors in SMNF)
                  -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
newMergeCaseExprs kv ng eenv1 eenv2 m_id m_ns bind1 as1 bind2 as2 =
    let
        as_info1 = map (smnfAltInfo bind1) as1
        as_info2 = map (smnfAltInfo bind2) as2
    in
    newMergeIntoCase kv ng eenv1 eenv2 m_id m_ns $ as_info1 ++ as_info2

newMergeIntoCase :: KnownValues
                 -> NameGen
                 -> ExprEnv
                 -> ExprEnv
                 -> MergeId
                 -> MergedIds
                 -> [(DataCon, Id, Integer, Expr)]
                 -> (Expr, MergedIds, [PathCond], HS.HashSet Id, NameGen)
newMergeIntoCase kv ng eenv1 eenv2 m_id m_ns b_as =
    let
        -- Group up by common data constructors
        as_hm = foldr (\(DataCon n _, i, l, e) -> HM.insertWith (++) n [(i, l, e)]) HM.empty $ b_as
        as_grouped = HM.toList as_hm :: [(Name, [(Id, Integer, Expr)])]

        -- Form the new case
        num_grouped = zip [1..] (map snd as_grouped) :: [(Integer, [(Id, Integer, Expr)])]
        ((m_ns', pc', symbs', ng'), new_alts) =
                  L.mapAccumL
                          (\(m_ns_, pc_, symbs_, ng_) (i, es) ->
                              let
                                  (e', m_ns_', pc_', symbs_', ng_') = newMergeExprs kv ng_ eenv1 eenv2 m_id (HM.union m_ns m_ns_) (map thd3 es)
                              in
                              ((m_ns_' `HM.union` m_ns_, pc_ ++ pc_', symbs_ `HS.union` symbs_', ng_'), Alt (LitAlt $ LitInt i) e')
                          )
                          (HM.empty, [], HS.empty, ng) num_grouped

        (new_bndee, ng'') = freshId TyLitInt ng'
        (new_bnd, ng''') = freshId TyLitInt ng''

        bndee_pc = mkBounds (Var new_bndee) 1 (toInteger $ length num_grouped)
        link_pc = map (\(i, j_es) -> mkMergeCasePC kv new_bndee i
                                   $ map (\(bnd_, lit_, _) -> (bnd_, lit_)) j_es)
                      num_grouped
    in
    (Case (Var new_bndee) new_bnd new_alts, m_ns', bndee_pc ++ link_pc ++ pc', HS.insert new_bndee symbs', ng''')
    where
      fst3 (x, _, _) = x
      snd3 (_, x, _) = x
      thd3 (_, _, x) = x

smnfAltInfo :: Id -> Alt -> (DataCon, Id, Integer, Expr)
smnfAltInfo i (Alt (LitAlt (LitInt l)) e)
    | Data dc:_ <- unApp e = (dc, i, l, e)
smnfAltInfo _ a = error $ "smnfAltInfo: invalid Alt structure" ++ show a

mkMergeCasePC :: KnownValues -> Id -> Integer -> [(Id, Integer)] -> PathCond
mkMergeCasePC kv bind1 l bls =
      flip ExtCond True
    . mkEqExpr kv (mkEqExpr kv (Var bind1) (Lit $ LitInt l)) 
    $ foldr (mkOrExpr kv)
            (mkFalse kv)
            (map (\(b2, jl) -> mkEqExpr kv (Var b2) (Lit (LitInt jl))) bls)

resolveNewVariables :: TypeEnv
                    -> KnownValues
                    -> NameGen
                    -> MergeId
                    -> MergedIds
                    -> SymbolicIds
                    -> ExprEnv
                    -> ExprEnv
                    -> ExprEnv
                    -> (ExprEnv, [PathCond], SymbolicIds, NameGen)
resolveNewVariables tenv kv ng m_id m_ns = resolveNewVariables' m_ns [] tenv kv ng m_id m_ns

resolveNewVariables' :: MergedIds
                     -> [PathCond]
                     -> TypeEnv
                     -> KnownValues
                     -> NameGen
                     -> MergeId
                     -> MergedIds
                     -> SymbolicIds
                     -> ExprEnv
                     -> ExprEnv
                     -> ExprEnv
                     -> (ExprEnv, [PathCond], SymbolicIds, NameGen)
resolveNewVariables' r_m_ns pc tenv kv ng m_id m_ns symbs eenv1 eenv2 n_eenv
    | HM.null r_m_ns = (n_eenv, pc, symbs, ng)
    | otherwise =
        let
            (n_eenv', m_ns', r_m_ns', pc', symbs', ng') =
                foldr (\((n1, n2), i) (n_eenv_, m_ns_, r_m_ns_, pc_, symbs_, ng_) ->
                          let
                              t = typeOf i
                              v1 = Var $ Id n1 t
                              v2 = Var $ Id n2 t

                              (n_eenv_', r_m_ns_', pc_', symbs_', ng_') =
                                      if | E.isSymbolic n1 eenv1
                                         , E.isSymbolic n2 eenv2
                                         , isPrimType t ->
                                              let
                                                  (si, ng__) = freshId t ng_
                                                  pc__ = [ PC.mkAssumePC m_id 1 $ ExtCond (mkEqPrimExpr t kv (Var si) v1) True
                                                         , PC.mkAssumePC m_id 2 $ ExtCond (mkEqPrimExpr t kv (Var si) v2) True ]
                                              in
                                              ( E.insertSymbolic (idName si) si n_eenv_
                                              , HM.empty
                                              , pc__
                                              , HS.singleton si
                                              , ng__)
                                          | E.isSymbolic n1 eenv1
                                          , E.isSymbolic n2 eenv2
                                          , not (n1 `E.member` eenv2)
                                          , not (n2 `E.member` eenv1) ->
                                              let
                                                  eenv = E.insert n2 v1 $ E.insert (idName i) v1 n_eenv_
                                              in
                                              ( eenv
                                              , HM.empty
                                              , []
                                              , HS.empty
                                              , ng_)
                                          | E.isSymbolic n1 eenv1
                                          , E.isSymbolic n2 eenv2 ->
                                              let
                                                  (e1, pc1', f_symb1, ng_') = arbDCCase tenv ng_ t
                                                  (e2, pc2', f_symb2, ng_'') = arbDCCase tenv ng_' t
                                                  (e_m, m_ns', pc'', f_symb3, ng_''') =
                                                      newMergeExpr kv ng_'' m_id (HM.union m_ns_ r_m_ns_) eenv1 eenv2 e1 e2
                                              in
                                              ( E.insert n1 e1 . E.insert n2 e2 $ E.insert (idName i) e_m n_eenv_
                                              , m_ns'
                                              , pc' ++ pc2' ++ pc''
                                              , f_symb1 `HS.union` f_symb2 `HS.union` f_symb3
                                              , ng_''')
                                          | otherwise ->
                                                  let
                                                      (e_, pc__, _, ng__) = newCaseExpr ng_ m_id v1 v2
                                                  in
                                                  (E.insert (idName i) e_ n_eenv_, HM.empty, pc__, HS.empty, ng__)

                          in
                          ( n_eenv_'
                          , HM.union m_ns_ r_m_ns_'
                          , HM.union r_m_ns_ r_m_ns_'
                          , pc_ ++ pc_
                          , HS.union symbs_ symbs_'
                          , ng_'))
                      (n_eenv, m_ns, HM.empty, [], symbs, ng)
                      (HM.toList r_m_ns)
        in
        resolveNewVariables' r_m_ns' (pc ++ pc') tenv kv ng' m_id m_ns' symbs' eenv1 eenv2 n_eenv'

------------------------------------------------

-- | Either (i) Inline var with value from ExprEnv (if any)
-- , (ii) Renames corresponding Vars in the 2 Exprs to a new, common Var
-- , or (iii) Concretizes symbolic var to case expression on its Data Constructors if necessary.
-- Only do (i) if it hasn't been inlined till then, to prevent infinite recursion in the case of merging 2 infinite exprs.
-- e.g. merging x = x:xs and y = y:ys
inlineExpr :: Named t
           => Context t -> HS.HashSet Name -> HS.HashSet Name -> Expr -> Expr
           -> (Context t, Expr, Expr)
inlineExpr ctxt@(Context { s1_ = (State {expr_env = eenv1}), s2_ = (State {expr_env = eenv2})}) inlined1 inlined2 e1 e2 =
    let (e1', inlined1') = inlineVar eenv1 inlined1 e1
        (e2', inlined2') = inlineVar eenv2 inlined2 e2
    in inlineExpr' ctxt inlined1' inlined2' e1' e2'

{-# INLINE inlineVar #-}
inlineVar :: E.ExprEnv -> HS.HashSet Name -> Expr -> (Expr, HS.HashSet Name)
inlineVar eenv inlined e
    | (Var (Id n _)) <- e
    , not $ HS.member n inlined
    , Just e' <- E.deepLookup n eenv = (e', HS.insert n inlined)
    | otherwise = (e, inlined)

inlineExpr' :: Named t
            => Context t -> HS.HashSet Name -> HS.HashSet Name -> Expr -> Expr
            -> (Context t, Expr, Expr)
inlineExpr' ctxt inlined1 inlined2 (App e1 e2) (App e3 e4)
    | isMergeableExpr (expr_env (s1_ ctxt)) (expr_env (s2_ ctxt)) e1 e3 =
        let (ctxt', e1', e3') = inlineExpr ctxt inlined1 inlined2 e1 e3
            (ctxt'', e2', e4') = inlineExpr ctxt' inlined1 inlined2 e2 e4
        in (ctxt'', (App e1' e2'), (App e3' e4'))
inlineExpr' ctxt _ _ e1@(Var _) e2@(Var _)
    | e1 == e2 = (ctxt, e1, e2)
    | otherwise = mergeVars ctxt e1 e2
inlineExpr' ctxt@(Context { s1_ = s1, s2_ = s2}) _ _ e1@(Var i) e2@(Case _ _ _)
    | isSMNF (expr_env s2) e2
    , HS.member i (symbolic_ids s1)
    , not $ isPrimType (idType i) =
        let (ctxt', e1') = symToCase ctxt e1 True
        in (ctxt', e1', e2)
inlineExpr' ctxt@(Context { s1_ = s1, s2_ = s2}) _ _ e1@(Case _ _ _) e2@(Var i)
    | isSMNF (expr_env s1) e1
    , HS.member i (symbolic_ids s2)
    , not $ isPrimType (idType i) =
        let (ctxt', e2') = symToCase ctxt e2 False
        in (ctxt', e1, e2')
inlineExpr' ctxt _ _ e1 e2 = (ctxt, e1, e2)

mergeVars :: Named t
           => Context t -> Expr -> Expr
           -> (Context t, Expr, Expr)
mergeVars ctxt@(Context {s1_ = s1, s2_ = s2, renamed1_ = renamed1, renamed2_ = renamed2, ng_ = ng}) (Var i1) (Var i2)
    | i1 == i2 = (ctxt, Var i1, Var i2)
    | (idType i1 == idType i2)
    , not $ E.member (idName i1) (expr_env s2) -- if both are symbolic variables unique to their states, replace one of them with the other
    , not $ E.member (idName i2) (expr_env s1)
    , HS.member i1 (symbolic_ids s1)
    , HS.member i2 (symbolic_ids s2) =
        let s2' = mergeReplaceVar s2 i2 i1
        in (ctxt {s2_ = s2'}, Var i1, Var i1)
    | idType i1 == idType i2
    , not $ elem (idName i1) (HM.elems renamed1) -- check if symbolic var is a var that is a result of some previous renaming when merging the Expr
    , not $ elem (idName i2) (HM.elems renamed2)
    , HS.member i1 (symbolic_ids s1)
    , HS.member i2 (symbolic_ids s2) =
        let (newSymId, ng') = freshMergeId (idType i1) ng
            s1' = mergeReplaceVar s1 i1 newSymId 
            s2' = mergeReplaceVar s2 i2 newSymId
            ctxt' = ctxt { ng_ = ng', s1_ = s1', s2_ = s2', renamed1_ = HM.insert (idName i1) (idName newSymId) renamed1
                         , renamed2_ = HM.insert (idName i2) (idName newSymId) renamed2 }
        in (ctxt', Var newSymId, Var newSymId)
    | otherwise = (ctxt, Var i1, Var i2)
mergeVars _ e1 e2 = error $ "Non-Var Exprs. " ++ (show e1) ++ "\n" ++ (show e2)

mergeReplaceVar :: Named t => State t -> Id -> Id -> State t
mergeReplaceVar s@(State {known_values = kv, path_conds = pc, symbolic_ids = syms, expr_env = eenv}) old new = if isPrimType (idType old)
    then s { path_conds = PC.insert (ExtCond (mkEqPrimExpr (idType old) kv (Var new) (Var old)) True) pc
           , symbolic_ids = HS.insert new syms
           , expr_env = E.insertSymbolic (idName new) new eenv}
    else (rename (idName old) (idName new) s)
            { expr_env = E.insertSymbolic (idName new) new $ E.insert (idName old) (Var new) eenv
            , symbolic_ids = HS.insert new (HS.delete old syms)}

-- | Replace Symbolic Variable with a Case Expression, where each Alt is a Data Constructor
symToCase :: Named t => Context t -> Expr -> Bool -> (Context t, Expr)
symToCase ctxt@(Context { s1_ = s1, s2_ = s2, ng_ = ng, newPCs_ = newPCs }) (Var i) first =
    let s = if first then s1 else s2
        (adt, bi) = fromJust $ getCastedAlgDataTy (idType i) (type_env s)
        dcs = dataConsFromADT adt
        (newId, ng') = freshMergeId TyLitInt ng

        ((s', ng''), dcs') = L.mapAccumL (concretizeSym bi Nothing) (s, ng') dcs

        e2 = createCaseExpr newId dcs'
        syms' = HS.delete i $ HS.insert newId (symbolic_ids s')
        eenv' = E.insert (idName i) e2 (expr_env s')

        -- add PC restricting range of values for newSymId
        lower = 1
        newSymConstraint = restrictSymVal (known_values s) lower (toInteger $ length dcs) newId

        s'' = s' {symbolic_ids = syms', expr_env = eenv'}
    in if first
        then (ctxt { s1_ = s'', ng_ = ng'', newPCs_ = newSymConstraint:newPCs}, e2)
        else (ctxt { s2_ = s'', ng_ = ng'', newPCs_ = newSymConstraint:newPCs}, e2)
symToCase _ e1 _ = error $ "Unhandled Expr: " ++ (show e1)

-- | Creates and applies new symbolic variables for arguments of Data Constructor
concretizeSym :: [(Id, Type)] -> Maybe Coercion -> (State t, NameGen) -> DataCon -> ((State t, NameGen), Expr)
concretizeSym bi maybeC (s, ng) dc@(DataCon n ts) =
    let dc' = Data dc
        ts' = anonArgumentTypes $ PresType ts
        ts'' = foldr (\(i, t) e -> retype i t e) ts' bi
        (ns, ng') = freshNames (length ts'') ng
        newParams = map (\(n', t) -> Id n' t) (zip ns ts'')
        ts2 = map snd bi
        dc'' = mkApp $ dc' : (map Type ts2) ++ (map Var newParams)
        dc''' = case maybeC of
            (Just (t1 :~ t2)) -> Cast dc'' (t2 :~ t1)
            Nothing -> dc''
        eenv = foldr (uncurry E.insertSymbolic) (expr_env s) $ zip (map idName newParams) newParams
        syms = foldr HS.insert (symbolic_ids s) newParams
    in ((s {expr_env = eenv, symbolic_ids = syms} , ng'), dc''')


mergeInlinedExpr :: Named t => Context t -> Expr -> Expr -> (Context t, Expr)
mergeInlinedExpr ctxt@(Context {newId_ = newId}) (App e1 e2) (App e3 e4)
    | isMergeableExpr (expr_env (s1_ ctxt)) (expr_env (s2_ ctxt)) e1 e3 =
        let (ctxt', e1') = mergeInlinedExpr ctxt e1 e3
            (ctxt'', e2') = mergeInlinedExpr ctxt' e2 e4
        in (ctxt'', App e1' e2')
    | otherwise = (ctxt, createCaseExpr newId [(App e1 e2), (App e3 e4)])
mergeInlinedExpr ctxt@(Context { s1_ = s1, s2_ = s2 }) e1@(Case _ _ _) e2
    | isSMNF (expr_env s1) e1
    , isSMNF (expr_env s2) e2 = mergeCase ctxt e1 e2
mergeInlinedExpr ctxt@(Context { s1_ = s1, s2_ = s2 }) e1 e2@(Case _ _ _)
    | isSMNF (expr_env s1) e1
    , isSMNF (expr_env s2) e2 = mergeCase ctxt e1 e2
mergeInlinedExpr ctxt (Lit l1) (Lit l2)
    | l1 == l2 = (ctxt, Lit l1)
    | (typeOf l1) == (typeOf l2) = mergeLits ctxt l1 l2
mergeInlinedExpr ctxt (Var i) (Lit l)
    | (typeOf i) == (typeOf l) = mergeVarLit ctxt i l True
mergeInlinedExpr ctxt (Lit l) (Var i)
    | (typeOf i) == (typeOf l) = mergeVarLit ctxt i l False
mergeInlinedExpr ctxt@(Context { newId_ = newId }) e1 e2
    | e1 == e2 = (ctxt, e1)
    | otherwise = (ctxt, createCaseExpr newId [e1, e2])

-- | Combines 2 Lits `l1` and `l2` into a single new Symbolic Variable and adds new Path Constraints
mergeLits :: Context t -> Lit -> Lit -> (Context t, Expr)
mergeLits ctxt@(Context {newId_ = newId, newSyms_ = newSyms, newPCs_ = newPCs, ng_ = ng}) l1 l2 =
    let (newSymId, ng') = freshMergeId (typeOf l1) ng
        newSyms' = HS.insert newSymId newSyms
        pc1 = PC.mkAssumePC newId 1 (AltCond l1 (Var newSymId) True)
        pc2 = PC.mkAssumePC newId 2 (AltCond l2 (Var newSymId) True)
    in (ctxt { newSyms_ = newSyms', newPCs_ = pc1:pc2:newPCs, ng_ = ng' }, Var newSymId)

-- | Combines a lit `l` and variable `i` into a single new Symbolic Variable and adds new Path Constraints
mergeVarLit :: Context t -> Id -> Lit -> Bool -> (Context t, Expr)
mergeVarLit ctxt@(Context {s1_ = s1, newId_ = newId, newSyms_ = newSyms, newPCs_ = newPCs, ng_ = ng}) i l first =
    let (newSymId, ng') = freshMergeId (typeOf l) ng
        newSyms' = HS.insert newSymId newSyms
        pc1 = AltCond l (Var newSymId) True
        pc2 = ExtCond (mkEqPrimExpr (typeOf i) (known_values s1) (Var i) (Var newSymId)) True
        pcs' = case first of
            True -> [PC.mkAssumePC newId 1 pc2, PC.mkAssumePC newId 2 pc1]
            False -> [PC.mkAssumePC newId 1 pc1, PC.mkAssumePC newId 2 pc2]
    in (ctxt { newSyms_ = newSyms', newPCs_ = pcs' ++ newPCs, ng_ = ng' }, Var newSymId)

type Conds = [(Id, Integer)]

-- | Given 2 Exprs such as:
-- Case n of (1 -> A e f, 2 -> B g h), and
-- Case m of (1 -> B g f, 2 -> A f h), merges them to form:
-- Case new of
--      1 -> A (Case new' of 1 -> e, 2 -> f) (Case new'' of 1 -> f, 2 -> h)
--      2 -> B g (Case new''' of 1 -> h, 2 -> f)
-- With new PathConds:
-- NOT (new = 1) OR ((NOT (new' = 1) OR (n = 1)) AND (NOT (new' = 1) OR (m = 2)) AND (NOT (new'' = 1) OR (n = 1)) AND (NOT (new'' = 2) OR (m = 2)))
-- NOT (new = 2) OR ((NOT (new''' = 1) OR (n = 2)) AND (NOT (new''' = 2) OR (m = 1)))
mergeCase :: Named t
          => Context t -> Expr -> Expr
          -> (Context t, Expr)
mergeCase ctxt@(Context { newId_ = newId}) e1 e2 =
    let choices = (getChoices e1 newId 1) ++ (getChoices e2 newId 2)
    in mergeCase' ctxt choices

mergeCase' :: Named t
          => Context t -> [(Conds, Expr)]
          -> (Context t, Expr)
mergeCase' ctxt@(Context { s1_ = s1@(State {known_values = kv}), s2_ = s2, ng_ = ng, newId_ = newId, newPCs_ = newPCs, newSyms_ = syms }) choices =
    let groupedChoices = groupChoices choices
        (ctxt', merged) = L.mapAccumR mergeChoices (emptyContext s1 s2 ng newId) groupedChoices

        newSyms = newSyms_ ctxt'
        ng' = ng_ ctxt'
        (newSymId, ng'') = freshMergeId TyLitInt ng'
        newSyms' = HS.insert newSymId newSyms

        mergedExprs = map fst merged
        mergedExpr = createCaseExpr newSymId mergedExprs
        newPCs' = map snd merged
        (upper, newPCs'') = bindExprToNum (\num pc -> impliesPC kv newSymId num pc) newPCs' -- note: binding here is same as in createCaseExpr

        -- add PC restricting range of values for newSymId
        lower = 1
        newSymConstraint = restrictSymVal kv lower (upper - 1) newSymId
        newPCs''' = newSymConstraint:newPCs''

        ctxt'' = ctxt {newPCs_ = newPCs''' ++ newPCs, newSyms_ = HS.union newSyms' syms, ng_ = ng''}
    in (ctxt'', mergedExpr)

-- | Given a list of (Conds, Expr) with the same inner DataCon, merges the
-- Exprs recursively into 1 Expr, along with an associated PathCond formed
-- from the given Conds
mergeChoices :: Named t => Context t -> [(Conds, Expr)] -> (Context t, (Expr, PathCond))
mergeChoices ctxt@(Context {s1_ = (State { known_values = kv }) }) [choice] =
    let pc = ExtCond (condsToExpr kv (fst choice)) True
    in (ctxt , (snd choice, pc))
mergeChoices ctxt@(Context { s1_ = (State { known_values = kv}) }) choices@(_:_) =
        -- apps :: [(Conds, [Expr])], split up each choice into a sequence of sub-Exprs
    let apps = map (\(cs, e) -> (cs, unApp e)) choices
        -- appsWConds :: [[(Conds, Expr)]], for each `[Expr]` in apps, pair the common `Conds` with each `Expr` in the list
        appsWConds = map (\(cs, e) -> map (\x -> (cs, x)) e) apps
        -- appsWCondsT :: [[(Conds, Expr)]], where each `[(Conds, Expr)]` is a list of choices for that sub-Expr in the merged Expr
        appsWCondsT = L.transpose appsWConds
        -- split the appsWCondsT into 2 lists, where first list contains sub-Exprs that are equal among all the choices
        (common, rest) = L.span (\ls -> (length . L.nub $ (map snd ls)) == 1) appsWCondsT
        (ctxt', restMerged) = L.mapAccumR mergeCase' ctxt rest
        -- get just the Exprs (add PathConds later)
        common' = map (snd . head) common
        apps' = common' ++ restMerged
        mergedExpr = mkApp apps'

        newPCs = case restMerged of
            -- 'AND' all `Conds` for each Expr and `OR` these combined Conds together
            [] -> (\e -> [ExtCond e True]) . dnf kv $ map (condsToExpr kv . fst) choices
            _ -> newPCs_ ctxt' -- PCs would have been added when merging tailApps
        newPCExprs = map (\(ExtCond e _) -> e) newPCs
        newPC = ExtCond (cnf kv newPCExprs) True
        ctxt'' = ctxt' {newPCs_ = []}
    in (ctxt'', (mergedExpr, newPC))
mergeChoices _ [] = error $ "Choices must be non empty"

-- | If `e` is a Case Expr, recursively gets list of nested Alt Exprs, along with (Id, Integer) pairs indicating the accumulated constraints
-- along the way. (Assumed that `e` is in SMNF)
-- e.g. getChoices Case x of (1 -> Case y of (1 -> A, 2 -> B), 2 -> Case z of (1 -> C, 2 -> D (Case w of 1 -> E, 2 -> F))) =
-- [([(x,1), (y,1)], A), ([(x,1), (y,2)], B), ([(x,2),(z,1)], C), ([(x,2),(z,2)], D (Case w of 1 -> E, 2 -> F))]
getChoices :: Expr -> Id -> Integer -> [(Conds, Expr)]
getChoices e newId num
    | (Case (Var i) _ a) <- e =
        let choices = concatMap (getChoices' i) a
            choices' = map (\(c, ex) -> (cond:c, ex)) choices
        in choices'
    | otherwise = [([cond], e)]
    where
        cond = (newId, num)

getChoices' :: Id -> Alt -> [(Conds, Expr)]
getChoices' i (Alt (LitAlt (LitInt l)) e) =
    let cond = (i, l)
        choices = getChoices'' e
        choices' = map (\(c, ex) -> (cond:c, ex)) choices
    in choices'
getChoices' alt _ = error $ "Unhandled Alt: " ++ (show alt)

getChoices'' :: Expr -> [(Conds, Expr)]
getChoices'' (Case (Var i) _ a) = concatMap (getChoices' i) a
getChoices'' e = [([], e)]

-- Group Exprs with common inner DataCon together
groupChoices :: [(Conds, Expr)] -> [[(Conds, Expr)]]
groupChoices xs = L.groupBy (\(_, e1) (_, e2) -> commonSubExpr e1 e2) $ L.sortBy (\(_, e1) (_, e2) -> compare e1 e2) xs

commonSubExpr :: Expr -> Expr -> Bool
commonSubExpr (App e1 _) (App e1' _) = commonSubExpr e1 e1'
commonSubExpr (Data dc1) (Data dc2) = dc1 == dc2
commonSubExpr e1 e2 = e1 == e2

-- Given list of (Id, Int) pairs, creates Expr equivalent to Conjunctive Normal Form of (Id == Int) values
condsToExpr :: KnownValues -> Conds -> Expr
condsToExpr kv c =
    let es = map (\(i, num) -> mkEqExpr kv (Var i) (Lit $ LitInt num)) c
    in cnf kv es

-- Given an `ExtCond e b`, and an `Id`, `Int` pair, modifies `e` to (NOT (Id == Int)) OR e
impliesPC :: KnownValues -> Id -> Integer -> PathCond -> PathCond
impliesPC kv newId num (ExtCond e b) = implies kv newId num e b
impliesPC _ _ _ pc = error $ "Can only add clause to ExtCond. Got: " ++ (show pc)

-- Given an Expr `e`, and an `Id`, `Int` pair, returns `ExtCond ((NOT (Id == Int)) OR e) True`
implies :: KnownValues -> Id -> Integer -> Expr -> Bool -> PathCond
implies kv newId num e b = implies' kv (mkEqExpr kv (Var newId) (Lit $ LitInt num)) e b

implies' :: KnownValues -> Expr -> Expr -> Bool -> PathCond
implies' kv clause e b =
    let e' = mkImpliesExpr kv clause e
    in ExtCond e' b

-- | Merges 2 Exprs without inlining Vars from the expr_env or combining symbolic variables
-- Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D (Case x of 1 -> e_1, 2 -> e_1') (Case x of 1 -> e_2, 2 -> e_2') ...."

mergeExpr :: Id -> Expr -> Expr -> Expr
mergeExpr newId a1@(App e1 e2) a2@(App e1' e2') =
    if typeOf e1 .::. typeOf e1' && typeOf e2 .::. typeOf e2'
        then App (mergeExpr newId e1 e1') (mergeExpr newId e2 e2')
        else createCaseExpr newId [a1, a2]
mergeExpr newId e1 e2 =
    if (e1 == e2)
        then e1
        else createCaseExpr newId [e1, e2]

createCaseExpr :: Id -> [Expr] -> Expr
createCaseExpr _ [e] = e
createCaseExpr newId es@(_:_) =
    let
        -- We assume that PathCond restricting newId's range is added elsewhere
        (_, alts) = bindExprToNum (\num e -> Alt (LitAlt (LitInt num)) e) es
    in Case (Var newId) newId alts
createCaseExpr _ [] = error "No exprs"

bindExprToNum :: (Integer -> a -> b) -> [a] -> (Integer, [b])
bindExprToNum f es = L.mapAccumL (\num e -> (num + 1, f num e)) 1 es


mergeSymbolicIds :: Context t -> SymbolicIds
mergeSymbolicIds (Context { s1_ = (State {symbolic_ids = syms1}), s2_ = (State {symbolic_ids = syms2})
                          , newSyms_ = syms3, newId_ = newId}) =
    let
        syms' = HS.unions [syms1, syms2, syms3]
        syms'' = HS.insert newId syms'
    in syms''

-- | Keeps all EnvObjs found in only one ExprEnv, and combines the common (key, value) pairs using the mergeEnvObj function
mergeExprEnv :: Context t -> (Context t, E.ExprEnv)
mergeExprEnv ctxt@(Context {s1_ = (State {expr_env = eenv1}), s2_ = (State {expr_env = eenv2}), newId_ = newId, ng_ = ngen, newSyms_ = newSyms}) =
    let
        (mergedEnvs, (changedSyms1, changedSyms2, ngen')) =
            S.runState (E.mergeAEnvObj
                              E.preserveMissing
                              E.preserveMissing
                              (E.zipWithAMatched (mergeEnvObj newId eenv1 eenv2)) 
                              eenv1 
                              eenv2) (HM.empty, HM.empty, ngen)
        newSyms' = (HM.elems changedSyms1) ++ (HM.elems changedSyms2) ++ (HS.toList newSyms)
        mergedEnvs' = foldr (\i@(Id n _) m -> E.insertSymbolic n i m) mergedEnvs newSyms'
        ctxt' = ctxt {ng_ = ngen'}
        -- rename any old Syms in PathConds in each state to their new Names, based on list of pairs in changedSyms1_ and changedSyms2_
        ctxt'' = updatePCs ctxt' changedSyms1 changedSyms2
        ctxt''' = updateSymbolicIds ctxt'' changedSyms1 changedSyms2
    in (ctxt''', mergedEnvs')

mergeEnvObj :: Id -> E.ExprEnv -> E.ExprEnv -> Name -> E.EnvObj -> E.EnvObj
            -> S.State (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) E.EnvObj
mergeEnvObj newId eenv1 eenv2 _ eObj1 eObj2
    | E.EqFast eObj1 == E.EqFast eObj2 = return eObj1
    -- Following cases deal with unequal EnvObjs
    | (E.ExprObj _ e1) <- eObj1
    , (E.ExprObj _ e2) <- eObj2 = return $ E.ExprObj Nothing (mergeExpr newId e1 e2)
    -- Replace the Id in the SymbObj with a new Symbolic Id and merge with the expr from the ExprObj in a Case expr
    | (E.SymbObj i) <- eObj1
    , (E.ExprObj _ e2) <- eObj2 = mergeSymbExprObjs newId i e2 True
    | (E.ExprObj _ e1) <- eObj1
    , (E.SymbObj i) <- eObj2 = mergeSymbExprObjs newId i e1 False
    -- Lookup RedirObj and create a Case Expr combining the lookup result with the expr from the ExprObj
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj _ e2) <- eObj2 = mergeRedirExprObjs newId eenv1 n e2 True
    | (E.ExprObj _ e1) <- eObj1
    , (E.RedirObj n) <- eObj2 = mergeRedirExprObjs newId eenv2 n e1 False
    | (E.RedirObj n1) <- eObj1
    , (E.RedirObj n2) <- eObj2 = mergeTwoRedirObjs newId eenv1 eenv2 n1 n2
    -- case of same name pointing to unequal SymbObjs shouldn't occur
    | (E.SymbObj i1) <- eObj1
    , (E.SymbObj i2) <- eObj2 = mergeTwoSymbObjs newId i1 i2
    | otherwise = error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

-- | If same name `n` points to a symbolic x@(Var (Id n _)) and Expr `e` in the 2 states, replace `x` with new symbolic variable `x'` and merge
-- both `e` and `x'`
mergeSymbExprObjs :: Id -> Id -> Expr -> Bool
                  -> S.State (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) E.EnvObj
mergeSymbExprObjs newId i@(Id _ t) e first = do
        (changedSyms1, changedSyms2, ngen) <- S.get
        let (newSymId, ngen') = freshMergeId t ngen
        -- Bool @`first` signifies which state the Id/Expr belongs to. Needed to ensure they are enclosed under the right `Assume` in the Case Exprs
        case first of
            True -> do
                let changedSyms1' = HM.insert i newSymId changedSyms1
                    mergedExprObj = E.ExprObj Nothing (mergeExpr newId (Var newSymId) e)
                S.put (changedSyms1', changedSyms2, ngen')
                return mergedExprObj
            False -> do
                let changedSyms2' = HM.insert i newSymId changedSyms2
                    mergedExprObj = E.ExprObj Nothing (mergeExpr newId e (Var newSymId))
                S.put (changedSyms1, changedSyms2', ngen')
                return mergedExprObj

mergeRedirExprObjs :: Id -> E.ExprEnv -> Name -> Expr -> Bool
                   -> S.State (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) E.EnvObj
mergeRedirExprObjs newId eenv n e first =
        let e2 = case (E.lookup n eenv) of
                Just x -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n)
            mergedEObj = case first of
                True -> E.ExprObj Nothing (mergeExpr newId e2 e)
                False -> E.ExprObj Nothing (mergeExpr newId e e2)
        in
        return mergedEObj

mergeTwoRedirObjs :: Id -> E.ExprEnv -> E.ExprEnv -> Name -> Name
                  -> S.State (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) E.EnvObj
mergeTwoRedirObjs newId eenv1 eenv2 n1 n2 =
        let e1 = case (E.lookup n1 eenv1) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n1)
            e2 = case (E.lookup n2 eenv2) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n2)
            mergedExprObj = E.ExprObj Nothing (mergeExpr newId e1 e2)
        in 
        return mergedExprObj

mergeTwoSymbObjs :: Id -> Id -> Id
                 -> S.State (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) E.EnvObj
mergeTwoSymbObjs newId i1@(Id _ t1) i2@(Id _ t2) = do
        (changedSyms1, changedSyms2, ngen) <- S.get
        let (newSymId1, ngen') = freshMergeId t1 ngen
            (newSymId2, ngen'') = freshMergeId t2 ngen'
            changedSyms1' = HM.insert i1 newSymId1 changedSyms1
            changedSyms2' = HM.insert i2 newSymId2 changedSyms2
            mergedExprObj = E.ExprObj Nothing (mergeExpr newId (Var newSymId1) (Var newSymId2))
        S.put (changedSyms1', changedSyms2', ngen'')
        return mergedExprObj

updatePCs :: Context t -> HM.HashMap Id Id -> HM.HashMap Id Id -> Context t
updatePCs ctxt@(Context { s1_ = s1@(State {path_conds = pc1}), s2_ = s2@(State {path_conds = pc2}) }) changedSyms1 changedSyms2 =
    let pc1' = subIdNamesPCs pc1 changedSyms1 -- update PathConds with new SymbolicIds from merging the expr_env
        pc2' = subIdNamesPCs pc2 changedSyms2
        s1' = s1 {path_conds = pc1'}
        s2' = s2 {path_conds = pc2'}
    in ctxt {s1_ = s1', s2_ = s2'}

updateSymbolicIds :: Context t -> HM.HashMap Id Id -> HM.HashMap Id Id -> Context t
updateSymbolicIds ctxt@(Context { s1_ = s1@(State {symbolic_ids = syms1}), s2_ = s2@(State {symbolic_ids = syms2}) }) changedSyms1 changedSyms2 =
    let
        oldSyms1 = HM.keys changedSyms1
        newSyms1 = HM.elems changedSyms1
        syms1' = HS.union (HS.fromList newSyms1) $ HS.difference syms1 (HS.fromList oldSyms1)
        oldSyms2 = HM.keys changedSyms2
        newSyms2 = HM.elems changedSyms2
        syms2' = HS.union (HS.fromList newSyms2) $ HS.difference syms2 (HS.fromList oldSyms2)
    in ctxt { s1_ = s1 { symbolic_ids = syms1' }, s2_ = s2 { symbolic_ids = syms2' } }

mergePathConds :: Simplifier simplifier => simplifier -> Context t -> (Context t, PathConds)
mergePathConds simplifier ctxt@(Context { s1_ = s1@(State { path_conds = pc1, known_values = kv })
                                         , s2_ = (State { path_conds = pc2 })
                                         , newId_ = newId
                                         , newPCs_ = newPCs}) =
    let        
        res_newId = ExtCond (mkOrExpr kv
                                (mkEqExpr kv (Var newId) (Lit $ LitInt 1))
                                (mkEqExpr kv (Var newId) (Lit $ LitInt 2))) True

        merged = PC.mergeWithAssumePCs newId pc1 pc2

        (s1', new') = L.mapAccumL (simplifyPC simplifier) s1 (res_newId:newPCs)
        new'' = concat new'

        merged' = foldr PC.insert merged new''

        merged'' = foldr (simplifyPCs simplifier s1') merged' new''
    in
    (ctxt { s1_ = s1' }, merged'')

-- | @`changedSyms` is list of tuples, w/ each tuple representing the old symbolic Id and the new replacement Id. @`subIdsPCs` substitutes all
-- occurrences of the old symbolic Ids' Names in the PathConds with the Name of the corresponding new Id. This assumes Old and New Id have the same type
subIdNamesPCs :: PathConds -> HM.HashMap Id Id -> PathConds
subIdNamesPCs pcs changedSyms =
    let
      changedSymsNames = HM.foldrWithKey (\k v hm -> HM.insert (idName k) (idName v) hm) HM.empty changedSyms
    in
    renames changedSymsNames pcs

-- | Return PathCond restricting value of `newId` to [lower, upper]
restrictSymVal :: KnownValues -> Integer -> Integer -> Id -> PathCond
restrictSymVal kv lower upper newId = ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var newId) lower) (mkLeIntExpr kv (Var newId) upper)) True

freshMergeId :: Type -> NameGen -> (Id, NameGen)
freshMergeId = freshSeededId (Name "m" Nothing 0 Nothing)