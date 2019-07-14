module G2.Execution.StateMerging
  ( mergeState
  , createEqExpr
  , createEqExprInt
  , mergeExpr
  , mergeExprEnv
  , mergeEnvObj
  , mergePathConds
  , mergePathCondsSimple
  , replaceNonDetWithSym
  , replaceCase
  , getAssumption
  , isSMAssumption
  ) where

import G2.Language
import G2.Execution.PrimitiveEval
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM

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
isMergeableExpr eenv1 eenv2 (Var i1) (Var i2)
    | (Just (E.Sym _)) <- E.lookupConcOrSym (idName i1) eenv1
    , (Just (E.Sym _)) <- E.lookupConcOrSym (idName i2) eenv2 = True
isMergeableExpr _ _ _ _ = False

mergeState :: (Eq t, Named t) => NameGen -> State t -> State t -> (NameGen, Maybe (State t))
mergeState ngen s1 s2 = 
    if isMergeable s1 s2
        then 
            let (newId, ngen') = freshId TyLitInt ngen
                (ngen'', curr_expr', s1', s2') = mergeCurrExpr ngen' s1 s2 newId
                (eenv', (changedSyms1, changedSyms2, ngen''')) = mergeExprEnv newId ngen'' (expr_env s1') (expr_env s2')
                pc1' = subIdNamesPCs (path_conds s1') changedSyms1 -- update PathConds with new SymbolicIds from merging the expr_env
                pc2' = subIdNamesPCs (path_conds s2') changedSyms2
                path_conds' = mergePathCondsSimple (known_values s1') newId pc1' pc2'
                syms' = mergeSymbolicIds (symbolic_ids s1') (symbolic_ids s2') newId (HM.union changedSyms1 changedSyms2)
            in (ngen'''
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
                             , rules = rules s1'
                             , num_steps = num_steps s1'
                             , track = track s1'
                             , tags = tags s1' }))
        else (ngen, Nothing)

mergeCurrExpr :: Named t => NameGen -> State t -> State t -> Id -> (NameGen, CurrExpr, State t, State t)
mergeCurrExpr ng s1@(State {curr_expr = ce1}) s2@(State {curr_expr = ce2}) newId
    | (CurrExpr evalOrRet1 e1) <- ce1
    , (CurrExpr evalOrRet2 e2) <- ce2
    , evalOrRet1 == evalOrRet2 =
        let (ng', ce', s1', s2', _, _) = mergeExprInline ng s1 s2 HM.empty HM.empty newId e1 e2
        in (ng', CurrExpr evalOrRet1 ce', s1', s2')
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."

-- | Merges 2 Exprs, combining 2 corresponding symbolic Vars into 1 if possible, and substituting the full Expr of any concrete Vars
mergeExprInline :: Named t
                => NameGen -> State t -> State t -> HM.HashMap Name Name -> HM.HashMap Name Name -> Id -> Expr -> Expr
                -> (NameGen, Expr, State t, State t, HM.HashMap Name Name, HM.HashMap Name Name)
mergeExprInline ng s1 s2 renamed1 renamed2 newId (App e1 e2) (App e3 e4) =
    let (ng', e1'', s1', s2', newNames1, newNames2) = mergeExprInline ng s1 s2 renamed1 renamed2 newId e1 e3
        -- For any symbolic variable pairs merged into new variables when merging `e1` and `e3`, rename all occurrences of
        -- the old symbolic vars in `e2` and `e4`
        e2' = renames newNames1 e2
        e4' = renames newNames2 e4
        renamed1' = HM.union renamed1 newNames1
        renamed2' = HM.union renamed2 newNames2
        (ng'', e2'', s1'', s2'', newNames1', newNames2') = mergeExprInline ng' s1' s2' renamed1' renamed2' newId e2' e4'
    in (ng'', App e1'' e2'', s1'', s2'', HM.union newNames1' newNames1, HM.union newNames2' newNames2)
mergeExprInline ng s1 s2 rn1 rn2 newId e1@(App _ _) (Var i) = mergeVarInline ng s1 s2 rn1 rn2 newId i e1 False
mergeExprInline ng s1 s2 rn1 rn2 newId (Var i) e2@(App _ _) = mergeVarInline ng s1 s2 rn1 rn2 newId i e2 True
mergeExprInline ng s1 s2 rn1 rn2 newId e1@(Var i1) e2@(Var i2)
    | e1 == e2 = (ng, e1, s1, s2, HM.empty, HM.empty)
    | otherwise =
        let maybeE1' = E.lookupConcOrSym (idName i1) (expr_env s1)
            maybeE2' = E.lookupConcOrSym (idName i2) (expr_env s2)
        in mergeVarsInline ng s1 s2 rn1 rn2 newId maybeE1' maybeE2'
mergeExprInline ng s1 s2 _ _ newId e1 e2
    | e1 == e2 = (ng, e1, s1, s2, HM.empty , HM.empty)
    | otherwise =
        let mergedExpr = createCaseExpr newId e1 e2
        in (ng, mergedExpr, s1, s2, HM.empty, HM.empty)

mergeVarInline :: (Named t)
               => NameGen -> State t -> State t -> HM.HashMap Name Name -> HM.HashMap Name Name -> Id -> Id -> Expr -> Bool
               -> (NameGen, Expr, State t, State t, HM.HashMap Name Name, HM.HashMap Name Name)
mergeVarInline ng s1 s2 renamed1 renamed2 newId i e@(App _ _) first =
    let eenv = if first then expr_env s1 else expr_env s2
        maybeE = E.lookupConcOrSym (idName i) eenv
    in case maybeE of
        (Just (E.Conc e')) -> if first
            then mergeExprInline ng s1 s2 renamed1 renamed2 newId e' e
            else mergeExprInline ng s1 s2 renamed1 renamed2 newId e e'
        (Just (E.Sym iSym)) ->
            let mergedExpr = if first
                then createCaseExpr newId (Var iSym) e
                else createCaseExpr newId e (Var iSym)
            in (ng, mergedExpr, s1, s2, HM.empty, HM.empty)
        Nothing -> error $ "Unable to find Var in expr_env: " ++ show i
mergeVarInline _ _ _ _ _ _ _ _ _ = error "mergeVarInline can only merge an Id with Expr of the form 'App _ _'"

mergeVarsInline :: Named t
                => NameGen -> State t -> State t -> HM.HashMap Name Name -> HM.HashMap Name Name -> Id -> Maybe E.ConcOrSym -> Maybe E.ConcOrSym
                -> (NameGen, Expr, State t, State t, HM.HashMap Name Name, HM.HashMap Name Name)
mergeVarsInline ng s1 s2 renamed1 renamed2 newId maybeE1 maybeE2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 = mergeExprInline ng s1 s2 renamed1 renamed2 newId e1 e2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Sym i)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId e1 (Var i)
        in (ng, mergedExpr, s1, s2, HM.empty, HM.empty)
    | (Just (E.Sym i)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId (Var i) e2
        in (ng, mergedExpr, s1, s2, HM.empty, HM.empty)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , i1 == i2 = (ng, Var i1, s1, s2, HM.empty, HM.empty)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , (idType i1 == idType i2)
    , not $ HS.member i1 (symbolic_ids s2)
    , not $ HS.member i2 (symbolic_ids s1) = -- if both are symbolic variables unique to their states, replace one of them with the other
        let s2' = rename (idName i2) (idName i1) s2
            syms' = HS.insert i1 (HS.delete i2 (symbolic_ids s2))
        in (ng, Var i1, s1, s2' {symbolic_ids = syms'}, HM.empty, HM.singleton (idName i2) (idName i1))
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , idType i1 == idType i2
    , not $ elem (idName i1) (HM.elems renamed1) -- check if symbolic var is a var that is a result of some previous renaming when merging the Expr
    , not $ elem (idName i2) (HM.elems renamed2) =
        let (newSymId, ng') = freshId (idType i1) ng
            s1' = rename (idName i1) (idName newSymId) s1
            s2' = rename (idName i2) (idName newSymId) s2
            syms1' = HS.insert newSymId (HS.delete i1 (symbolic_ids s1))
            syms2' = HS.insert newSymId (HS.delete i2 (symbolic_ids s2))
        in (ng', Var newSymId, s1' {symbolic_ids = syms1'}, s2' {symbolic_ids = syms2'}
           , HM.singleton (idName i1) (idName newSymId), HM.singleton (idName i2) (idName newSymId))
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId (Var i1) (Var i2)
        in (ng, mergedExpr, s1, s2, HM.empty, HM.empty)
    | otherwise = error "Unable to find Var(s) in expr_env"

-- | Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D NonDet[(Assume (x == 1) in e_1), (Assume (x == 2) in e_1')],..., NonDet[(Assume (x == 1) in e_n), (Assume (x == 2) in e_n')]" 
mergeExpr :: Id -> Expr -> Expr -> Expr
mergeExpr newId (App e1 e2) (App e1' e2') = App (mergeExpr newId e1 e1') (mergeExpr newId e2 e2')
mergeExpr newId e1 e1' = if (e1 == e1')
    then e1
    else createCaseExpr newId e1 e1'

createCaseExpr :: Id -> Expr -> Expr -> Expr
createCaseExpr newId e1 e2 =
    let
        alt1 = Alt (LitAlt (LitInt 1)) e1
        alt2 = Alt (LitAlt (LitInt 2)) e2
    -- PathCond restricting newId to 1 or 2 is added in mergePathConds
    in Case (Var newId) newId [alt1, alt2]

-- | Returns an Expr equivalent to "x == val", where x is a Var created from the given Id
createEqExprInt :: KnownValues -> Id -> Integer -> Expr
createEqExprInt kv newId val = createEqExpr kv newId (Lit (LitInt val))

createEqExpr :: KnownValues -> Id -> Expr -> Expr
createEqExpr kv newId e = App (App eq (Var newId)) e 
    where eq = mkEqPrimInt kv

mergeSymbolicIds :: SymbolicIds -> SymbolicIds -> Id -> HM.HashMap Id Id -> SymbolicIds
mergeSymbolicIds syms1 syms2 newId changedSyms =
    let syms' = HS.union syms1 syms2
        syms'' = HS.insert newId syms'
        oldSyms = HM.keys changedSyms
        newSyms = HM.elems changedSyms
        syms''' = HS.difference syms'' (HS.fromList oldSyms)
    in HS.union syms''' $ HS.fromList newSyms

-- | Keeps all EnvObjs found in only one ExprEnv, and combines the common (key, value) pairs using the mergeEnvObj function
mergeExprEnv :: Id -> NameGen -> E.ExprEnv -> E.ExprEnv -> (E.ExprEnv, (HM.HashMap Id Id, HM.HashMap Id Id, NameGen))
mergeExprEnv newId ngen eenv1 eenv2 = (E.wrapExprEnv $ M.unions [merged_map', eenv1_rem, eenv2_rem], (changedSyms1, changedSyms2, ngen'))
    where
        eenv1_map = E.unwrapExprEnv eenv1
        eenv2_map = E.unwrapExprEnv eenv2
        zipped_maps = (M.intersectionWith (\a b -> (a,b)) eenv1_map eenv2_map)
        ((changedSyms1, changedSyms2, ngen'), merged_map) = M.mapAccum (mergeEnvObj newId eenv1 eenv2) (HM.empty, HM.empty, ngen) zipped_maps
        newSyms = (HM.elems changedSyms1) ++ (HM.elems changedSyms2)
        merged_map' = foldr (\i@(Id n _) m -> M.insert n (E.SymbObj i) m) merged_map newSyms
        eenv1_rem = (M.difference eenv1_map eenv2_map)
        eenv2_rem = (M.difference eenv2_map eenv1_map)

mergeEnvObj :: Id -> E.ExprEnv -> E.ExprEnv -> (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) -> (E.EnvObj, E.EnvObj)
            -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeEnvObj newId eenv1 eenv2 (changedSyms1, changedSyms2, ngen) (eObj1, eObj2)
    | eObj1 == eObj2 = ((changedSyms1, changedSyms2, ngen), eObj1)
    -- Following cases deal with unequal EnvObjs
    | (E.ExprObj e1) <- eObj1
    , (E.ExprObj e2) <- eObj2 = ((changedSyms1, changedSyms2, ngen), E.ExprObj (mergeExpr newId e1 e2))
    -- Replace the Id in the SymbObj with a new Symbolic Id and merge with the expr from the ExprObj in a NonDet expr
    | (E.SymbObj i) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.SymbObj i) <- eObj2 = mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i e1 False
    -- Lookup RedirObj and create a NonDet Expr combining the lookup result with the expr from the ExprObj
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv1 n e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.RedirObj n) <- eObj2 = mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv2 n e1 False
    | (E.RedirObj n1) <- eObj1
    , (E.RedirObj n2) <- eObj2 = mergeTwoRedirObjs ngen changedSyms1 changedSyms2 newId eenv1 eenv2 n1 n2
    -- case of same name pointing to unequal SymbObjs shouldn't occur
    | (E.SymbObj i1) <- eObj1
    , (E.SymbObj i2) <- eObj2 = mergeTwoSymbObjs ngen changedSyms1 changedSyms2 newId i1 i2
    | otherwise = error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

-- | If same name `n` points to a symbolic x@(Var (Id n _)) and Expr `e` in the 2 states, replace `x` with new symbolic variable `x'` and merge
-- both `e` and `x'`
mergeSymbExprObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> Id -> Expr -> Bool
                  -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i@(Id _ t) e first =
        let (newSymId, ngen') = freshId t ngen
        -- Bool @`first` signifies which state the Id/Expr belongs to. Needed to ensure they are enclosed under the right `Assume` in the NonDet Exprs
        in case first of
            True ->
                let changedSyms1' = HM.insert i newSymId changedSyms1
                    mergedExprObj = E.ExprObj (mergeExpr newId (Var newSymId) e)
                in ((changedSyms1', changedSyms2, ngen'), mergedExprObj)
            False ->
                let changedSyms2' = HM.insert i newSymId changedSyms2
                    mergedExprObj = E.ExprObj (mergeExpr newId e (Var newSymId))
                in ((changedSyms1, changedSyms2', ngen'), mergedExprObj)

mergeRedirExprObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> E.ExprEnv -> Name -> Expr -> Bool
                   -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv n e first =
        let e2 = case (E.lookup n eenv) of
                Just x -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n)
            mergedEObj = case first of
                True -> E.ExprObj (mergeExpr newId e2 e)
                False -> E.ExprObj (mergeExpr newId e e2)
        in ((changedSyms1, changedSyms2, ngen), mergedEObj)

mergeTwoRedirObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> E.ExprEnv -> E.ExprEnv -> Name -> Name
                  -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoRedirObjs ngen changedSyms1 changedSyms2 newId eenv1 eenv2 n1 n2 =
        let e1 = case (E.lookup n1 eenv1) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n1)
            e2 = case (E.lookup n2 eenv2) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n2)
            mergedExprObj = E.ExprObj (mergeExpr newId e1 e2)
        in ((changedSyms1, changedSyms2, ngen), mergedExprObj)

mergeTwoSymbObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> Id -> Id
                 -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoSymbObjs ngen changedSyms1 changedSyms2 newId i1@(Id _ t1) i2@(Id _ t2) =
        let (newSymId1, ngen') = freshId t1 ngen
            (newSymId2, ngen'') = freshId t2 ngen'
            changedSyms1' = HM.insert i1 newSymId1 changedSyms1
            changedSyms2' = HM.insert i2 newSymId2 changedSyms2
            mergedExprObj = E.ExprObj (mergeExpr newId (Var newSymId1) (Var newSymId2))
        in ((changedSyms1', changedSyms2', ngen''), mergedExprObj)

-- | Simpler version of mergePathConds, may not be very efficient for large numbers of PCs, but suffices for simple cases
mergePathCondsSimple :: KnownValues -> Id -> PathConds -> PathConds -> PathConds
mergePathCondsSimple kv newId pc1 pc2 =
    let pc1HS = HS.fromList (PC.toList pc1)
        pc2HS = HS.fromList (PC.toList pc2)
        common = HS.toList $ HS.intersection pc1HS pc2HS
        pc1Only = HS.toList $ HS.difference pc1HS pc2HS
        pc2Only = HS.toList $ HS.difference pc2HS pc1HS
        pc1Only' = map (\pc -> AssumePC newId 1 pc) pc1Only
        pc2Only' = map (\pc -> AssumePC newId 2 pc) pc2Only
        mergedPC = PC.fromList common
        mergedPC' = foldr PC.insert mergedPC (pc1Only' ++ pc2Only')
        mergedPC'' = PC.insert (ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var newId) 1) (mkEqIntExpr kv (Var newId) 2)) True) mergedPC'
    in mergedPC''

-- | Does not always work if 2 top level AssumePCs both impose constraints on the same Name -> resulting in model generating conflicting values
-- and one being arbitrarily chosen over the other
mergePathConds :: KnownValues -> Id -> PathConds -> PathConds -> PathConds
mergePathConds kv newId pc1 pc2 = 
    -- If a key exists in both maps, then the respective values are combined and inserted into pc1_map'. 
    -- Else, all other values in pc1_map are added to pc1_map' as it is.
    -- pc2_map' will only contain values whose keys are not present in pc1_map
    let
        pc2_map = PC.toMap pc2
        pc1_map = PC.toMap pc1
        ((pc2_map', newAssumePCs), pc1_map') = M.mapAccumWithKey (mergeMapEntries newId) (pc2_map, HS.empty) pc1_map
        combined_map = PC.PathConds (M.union pc2_map' pc1_map')
        -- Add the following expression to constrain the value newId can take to either 1/2 when solving
        combined_map' = PC.insert (ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var newId) 1) (mkEqIntExpr kv (Var newId) 2)) True) combined_map
    in foldr PC.insert combined_map' newAssumePCs

-- A map and key,value pair are passed as arguments to the function. If the key exists in the map, then both values
-- are combined and the entry deleted from the map. Else the map and value are simply returned as it is.
mergeMapEntries :: Id -> (M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond)
                -> (Maybe Name)
                -> (HS.HashSet PC.PathCond, HS.HashSet Name)
                -> ((M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond), (HS.HashSet PC.PathCond, HS.HashSet Name))
mergeMapEntries newId (pc2_map, newAssumePCs) key (hs1, ns1) =
    case M.lookup key pc2_map of
        Just (hs2, ns2) -> ((pc2_map', newAssumePCs'), (mergedHS, mergedNS))
            where
                pc2_map' = M.delete key pc2_map
                (mergedHS, unmergedPCs) = mergeHashSets newId hs1 hs2
                mergedNS = HS.union ns1 ns2 -- names should still be the same even though some PCs are wrapped in AssumePCs and moved to different node
                newAssumePCs' = HS.union newAssumePCs unmergedPCs
        Nothing -> ((pc2_map, newAssumePCs), (hs1, ns1))

-- Any PathCond present in both HashSets is added as it is to the new HashSet.
-- A PathCond present in only 1 HashSet is changed to the form 'AssumePC (x == _) PathCond' and added to the new HashSet
mergeHashSets :: Id -> (HS.HashSet PathCond) -> (HS.HashSet PathCond) -> (HS.HashSet PathCond, HS.HashSet PathCond)
mergeHashSets newId hs1 hs2 = (common, unmergedPCs)
    where
        common = HS.intersection hs1 hs2
        hs1Minus2 = HS.difference hs1 hs2
        hs2Minus1 = HS.difference hs2 hs1
        hs1Minus2' = HS.map (\pc -> AssumePC newId 1 pc) hs1Minus2
        hs2Minus1' = HS.map (\pc -> AssumePC newId 2 pc) hs2Minus1
        unmergedPCs = HS.union hs1Minus2' hs2Minus1'

-- | @`changedSyms` is list of tuples, w/ each tuple representing the old symbolic Id and the new replacement Id. @`subIdsPCs` substitutes all
-- occurrences of the old symbolic Ids' Names in the PathConds with the Name of the corresponding new Id. This assumes Old and New Id have the same type
subIdNamesPCs :: PathConds -> HM.HashMap Id Id -> PathConds
subIdNamesPCs pcs changedSyms =
    let changedSymsNames = HM.foldrWithKey (\k v hm -> HM.insert (idName k) (idName v) hm) HM.empty changedSyms
    in renames changedSymsNames pcs

----------------
-- | Removes any NonDets in the expr_env and curr_expr by selecting one choice each time.
-- If NonDets are of the form `Assume (x == 1) e1 v Assume (x == 2) e2`, lookups the value of `x`
-- in the `Model` of the state and picks the corresponding Expr.

replaceCase :: State t -> State t
replaceCase s@(State {curr_expr = cexpr, expr_env = eenv}) =
    let eenv' = E.map (replaceCaseExpr s) eenv
        (CurrExpr eOrR e) = cexpr 
        cexpr' = CurrExpr eOrR (replaceCaseExpr s e)
    in (s {curr_expr = cexpr', expr_env = eenv'})

replaceCaseExpr :: State t -> Expr -> Expr
replaceCaseExpr s (App e1 e2) = App (replaceCaseExpr s e1) (replaceCaseExpr s e2)
replaceCaseExpr s@(State {model = m, type_classes = tc}) (Case e i alts) =
    let val = subExpr m tc e
    in case val of
        (Lit lit) ->
            let (Alt (LitAlt _) expr):_ = matchLitAlts lit alts
                binds = [(i, Lit lit)]
            in replaceCaseExpr s $ liftCaseBinds binds expr
        _ -> error $ "Unable to find Lit value for e. Got: " ++ show val
replaceCaseExpr _ e = e

-- | Looks up values in the `Model` of the state, substitutes into @`e`, and evaluates it
substAndEval :: State t -> Expr -> Bool
substAndEval (State {model = m
                    , known_values = kv
                    , type_classes = tc}) e =
    getBoolFromDataCon kv solvedExpr 
    where
        exprToSolve = subExpr m tc e
        solvedExpr = evalPrim kv exprToSolve

subExpr :: Model -> TypeClasses -> Expr -> Expr
subExpr m tc = modifyContainedASTs (subExpr' m tc [])

subExpr' :: Model -> TypeClasses -> [Id] -> Expr -> Expr
subExpr' m tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- M.lookup n m =
        subExpr' m tc (i:is) e
    | otherwise = v
subExpr' m tc is e = modifyChildren (subExpr' m tc is) e

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

liftCaseBinds :: [(Id, Expr)] -> Expr -> Expr
liftCaseBinds [] expr = expr
liftCaseBinds ((b, e):xs) expr = liftCaseBinds xs $ replaceASTs (Var b) e expr

-- | Given a NonDet Expr created by merging exprs, replaces it with a symbolic variable. Encodes the choices in the NonDet Expr as Path Constraints
-- Called from evalApp when App center is Prim
replaceNonDetWithSym :: State t -> NameGen -> Expr -> (State t, NameGen, Expr)
replaceNonDetWithSym s@(State {expr_env = eenv, path_conds = pc, known_values = kv, symbolic_ids = syms}) ng e@(NonDet (x:_)) =
    let newSymT = returnType x
        (newSym, ng') = freshId newSymT ng -- create new symbolic variable
        eenv' = E.insertSymbolic (idName newSym) newSym eenv
        syms' = HS.insert newSym syms
        pcs  = createPCs kv e newSym []
        pc' = foldr PC.insert pc pcs
    in (s {expr_env = eenv', path_conds = pc', symbolic_ids = syms'}, ng', Var newSym)
replaceNonDetWithSym s ng (App e1 e2) =
    let (s', ng', e1') = replaceNonDetWithSym s ng e1
        (s'', ng'', e2') = replaceNonDetWithSym s' ng' e2
    in (s'', ng'', (App e1' e2'))
replaceNonDetWithSym s ng e = (s,ng,e)

createPCs :: KnownValues -> Expr -> Id -> [PathCond] -> [PathCond]
createPCs kv (NonDet (x:xs)) newSymId pcs =
    case x of
        (Assume _ e1 e2) ->
            let (i, val) = getAssumption e1
            in case e2 of
                (NonDet _) ->
                    let newPCs = createPCs kv e2 newSymId []
                        newPCs' = map (\pc -> AssumePC i val pc) newPCs
                    in createPCs kv (NonDet xs) newSymId (newPCs' ++ pcs)
                _ ->
                    let pc = AssumePC i val $ ExtCond (createEqExpr kv newSymId e2) True
                    in createPCs kv (NonDet xs) newSymId (pc:pcs)
        _ -> error $ "NonDet option is of a wrong Data Constructor: " ++ (show x)
createPCs _ (NonDet []) _ pcs = pcs
createPCs _ _ _ pcs = pcs

getAssumption :: Expr -> (Id, Int)
getAssumption (App (App (Prim Eq _) (Var i)) (Lit (LitInt val))) = (i, fromInteger val)
getAssumption e = error $ "Unable to extract Id, Int from Assumed Expr: " ++ (show e)

-- | Returns True is Expr can be pattern matched against Assume-d Expr created during state merging
isSMAssumption :: Expr -> Bool
isSMAssumption (App (App (Prim Eq _) (Var _)) (Lit (LitInt _))) = True
isSMAssumption _ = False
