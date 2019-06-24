module G2.Execution.StateMerging
  ( mergeState
  , createEqExpr
  , createEqExprInt
  , replaceNonDets
  , mergeExpr
  , mergeExprEnv
  , mergeEnvObj
  , mergePathConds
  , mergePathCondsSimple
  , replaceNonDetWithSym
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
isMergeableExpr _ _ (Data _) (Data _) = True
isMergeableExpr eenv1 eenv2 (Var i1) (Var i2)
    | (Just (E.Sym _)) <- E.lookupConcOrSym (idName i1) eenv1
    , (Just (E.Sym _)) <- E.lookupConcOrSym (idName i2) eenv2 = True
isMergeableExpr _ _ _ _ = False

mergeState :: (Eq t, Named t) => NameGen -> State t -> State t -> (NameGen, Maybe (State t))
mergeState ngen s1 s2 = 
    if isMergeable s1 s2
        then 
            let (newId, ngen') = freshId TyLitInt ngen
                (curr_expr', s1', s2') = mergeCurrExprInl s1 s2 newId
                (expr_env', (changedSyms, ngen'')) = mergeExprEnv (known_values s1') newId ngen' (expr_env s1') (expr_env s2')
                syms' = mergeSymbolicIds (symbolic_ids s1') (symbolic_ids s2') newId changedSyms
                path_conds' = mergePathCondsSimple (known_values s1') newId (path_conds s1') (path_conds s2')
                path_conds'' = subIdNamesPCs path_conds' changedSyms -- update PathConds with new SymbolicIds from merging expr_envs
            in (ngen''
               , (Just State { expr_env = expr_env'
                             , type_env = type_env s1'
                             , curr_expr = curr_expr'
                             , path_conds = path_conds''
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

mergeCurrExprInl :: Named t => State t -> State t -> Id -> (CurrExpr, State t, State t)
mergeCurrExprInl s1@(State {curr_expr = ce1}) s2@(State {curr_expr = ce2}) newId
    | (CurrExpr evalOrRet1 e1) <- ce1
    , (CurrExpr evalOrRet2 e2) <- ce2
    , evalOrRet1 == evalOrRet2 =
        let (ce', s1', s2') = mergeExprInline s1 s2 newId e1 e2
        in (CurrExpr evalOrRet1 ce', s1', s2')
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."

mergeExprInline :: Named t => State t -> State t -> Id -> Expr -> Expr -> (Expr, State t, State t)
mergeExprInline s1 s2 newId (App e1 e2) (App e1' e2') =
    let (e1'', s1', s2') = mergeExprInline s1 s2 newId e1 e1'
        (e2'', s1'', s2'') = mergeExprInline s1' s2' newId e2 e2'
    in (App e1'' e2'', s1'', s2'')
mergeExprInline s1 s2 newId e1@(App _ _) (Var i) = mergeVarInline s1 s2 newId i e1 False
mergeExprInline s1 s2 newId (Var i) e2@(App _ _) = mergeVarInline s1 s2 newId i e2 True
mergeExprInline s1 s2 newId e1@(Var i1) e2@(Var i2)
    | e1 == e2 = (e1, s1, s2)
    | otherwise =
        let maybeE1' = E.lookupConcOrSym (idName i1) (expr_env s1)
            maybeE2' = E.lookupConcOrSym (idName i2) (expr_env s2)
        in mergeVarsInline s1 s2 newId maybeE1' maybeE2'
mergeExprInline s1 s2 newId e1 e2
    | e1 == e2 = (e1, s1, s2)
    | otherwise =
        let mergedExpr = NonDet [Assume Nothing (createEqExprInt kv newId 1) e1, Assume Nothing (createEqExprInt kv newId 2) e2]
            kv = known_values s1
        in (mergedExpr, s1, s2)

mergeVarInline :: (Named t) => State t -> State t -> Id -> Id -> Expr -> Bool -> (Expr, State t, State t)
mergeVarInline s1 s2 newId i e@(App _ _) first =
    let (eenv, kv) = if first then (expr_env s1, known_values s1) else (expr_env s2, known_values s2)
        maybeE = E.lookupConcOrSym (idName i) eenv
    in case maybeE of
        (Just (E.Conc e')) -> if first then mergeExprInline s1 s2 newId e' e else mergeExprInline s1 s2 newId e e'
        (Just (E.Sym iSym)) ->
            let mergedExpr = if first
                    then NonDet [Assume Nothing (createEqExprInt kv newId 1) (Var iSym), Assume Nothing (createEqExprInt kv newId 2) e]
                    else NonDet [Assume Nothing (createEqExprInt kv newId 1) e, Assume Nothing (createEqExprInt kv newId 2) (Var iSym)]
            in (mergedExpr, s1, s2)
        Nothing -> error $ "Unable to find Var in expr_env: " ++ show i
mergeVarInline _ _ _ _ _ _ = error "mergeVarInline can only merge an Id with Expr of the form 'App _ _'"

mergeVarsInline :: Named t => State t -> State t -> Id -> Maybe E.ConcOrSym -> Maybe E.ConcOrSym -> (Expr, State t, State t)
mergeVarsInline s1 s2 newId maybeE1 maybeE2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 = mergeExprInline s1 s2 newId e1 e2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Sym i)) <- maybeE2 =
        let mergedExpr = NonDet [Assume Nothing (createEqExprInt kv newId 1) e1, Assume Nothing (createEqExprInt kv newId 2) (Var i)]
        in (mergedExpr, s1, s2)
    | (Just (E.Sym i)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 =
        let mergedExpr = NonDet [Assume Nothing (createEqExprInt kv newId 1) (Var i), Assume Nothing (createEqExprInt kv newId 2) e2]
        in (mergedExpr, s1, s2)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , i1 == i2 = (Var i1, s1, s2)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , (idType i1 == idType i2)
    , not $ HS.member i1 (symbolic_ids s2)
    , not $ HS.member i2 (symbolic_ids s1) = -- if both are symbolic variables unique to their states, replace one of them with the other
        let s2' = rename (idName i2) (idName i1) s2
            eenv2' = E.redirect (idName i2) (idName i1) (expr_env s2')
        in (Var i1, s1, s2' {expr_env = eenv2'})
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2 =
        let mergedExpr = NonDet [Assume Nothing (createEqExprInt kv newId 1) (Var i1), Assume Nothing (createEqExprInt kv newId 2) (Var i2)]
        in (mergedExpr, s1, s2)
    | otherwise = error "Unable to find Var(s) in expr_env"
    where
        kv = known_values s1

-- | Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D NonDet[(Assume (x == 1) in e_1), (Assume (x == 2) in e_1')],..., NonDet[(Assume (x == 1) in e_n), (Assume (x == 2) in e_n')]" 
mergeExpr :: KnownValues -> Id -> Expr -> Expr -> Expr
mergeExpr kv newId (App e1 e2) (App e1' e2') = App (mergeExpr kv newId e1 e1') (mergeExpr kv newId e2 e2')
mergeExpr kv newId e1 e1' = if (e1 == e1') 
    then e1
    else NonDet [Assume Nothing (createEqExprInt kv newId 1) e1, Assume Nothing (createEqExprInt kv newId 2) e1']

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
mergeExprEnv :: KnownValues -> Id -> NameGen -> E.ExprEnv -> E.ExprEnv -> (E.ExprEnv, (HM.HashMap Id Id, NameGen))
mergeExprEnv kv newId ngen eenv1 eenv2 = (E.wrapExprEnv $ M.unions [merged_map', eenv1_rem, eenv2_rem], (changedSyms, ngen'))
    where eenv1_map = E.unwrapExprEnv eenv1
          eenv2_map = E.unwrapExprEnv eenv2
          zipped_maps = (M.intersectionWith (\a b -> (a,b)) eenv1_map eenv2_map)
          ((changedSyms, ngen'), merged_map) = M.mapAccum (mergeEnvObj kv newId eenv1 eenv2) (HM.empty, ngen) zipped_maps
          merged_map' = foldr (\i@(Id n _) m -> M.insert n (E.SymbObj i) m) merged_map (HM.elems changedSyms)
          eenv1_rem = (M.difference eenv1_map eenv2_map)
          eenv2_rem = (M.difference eenv2_map eenv1_map)

mergeEnvObj :: KnownValues -> Id
               -> E.ExprEnv
               -> E.ExprEnv
               -> (HM.HashMap Id Id, NameGen)
               -> (E.EnvObj, E.EnvObj)
               -> ((HM.HashMap Id Id, NameGen), E.EnvObj)
mergeEnvObj kv newId eenv1 eenv2 (changedSyms, ngen) (eObj1, eObj2)
    | eObj1 == eObj2 = ((changedSyms, ngen), eObj1)
    -- Following cases deal with unequal EnvObjs
    | (E.ExprObj e1) <- eObj1
    , (E.ExprObj e2) <- eObj2 = ((changedSyms, ngen), E.ExprObj (mergeExpr kv newId e1 e2))
    -- Replace the Id in the SymbObj with a new Symbolic Id and merge with the expr from the ExprObj in a NonDet expr
    | (E.SymbObj i) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeSymbExprObjs kv ngen changedSyms newId i e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.SymbObj i) <- eObj2 = mergeSymbExprObjs kv ngen changedSyms newId i e1 False
    -- Lookup RedirObj and create a NonDet Expr combining the lookup result with the expr from the ExprObj
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeRedirExprObjs kv ngen changedSyms newId eenv1 n e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.RedirObj n) <- eObj2 = mergeRedirExprObjs kv ngen changedSyms newId eenv2 n e1 False
    | (E.RedirObj n1) <- eObj1
    , (E.RedirObj n2) <- eObj2 = mergeTwoRedirObjs kv ngen changedSyms newId eenv1 eenv2 n1 n2
    | (E.SymbObj i1) <- eObj1
    , (E.SymbObj i2) <- eObj2 = mergeTwoSymbObjs kv ngen changedSyms newId i1 i2 -- case of same name pointing to unequal SymbObjs shouldn't occur
    | otherwise = error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

mergeSymbExprObjs :: KnownValues -> NameGen -> HM.HashMap Id Id -> Id -> Id -> Expr -> Bool -> ((HM.HashMap Id Id, NameGen), E.EnvObj)
mergeSymbExprObjs kv ngen changedSyms newId i@(Id _ t) e first =
        let (newSymId, ngen') = freshId t ngen
            changedSyms' = HM.insert i newSymId changedSyms
            -- Bool @`first` signifies which state the Id/Expr belongs to. Needed to ensure they are subsumed under the right `Assume` in the NonDet Exprs
            mergedExprObj = case first of
                                True -> E.ExprObj (mergeExpr kv newId (Var newSymId) e)
                                False -> E.ExprObj (mergeExpr kv newId e (Var newSymId))
        in ((changedSyms', ngen'), mergedExprObj)

mergeRedirExprObjs :: KnownValues -> NameGen -> HM.HashMap Id Id -> Id -> E.ExprEnv -> Name -> Expr -> Bool -> ((HM.HashMap Id Id, NameGen), E.EnvObj)
mergeRedirExprObjs kv ngen changedSyms newId eenv n e first =
        let e2 = case (E.lookup n eenv) of
                    (Just (Var (Id _ t))) -> Var (Id n t)
                    (Just x) -> x
                    Nothing -> error $ "Could not find EnvObj with name: " ++ (show n)
            mergedExprObj = case first of
                True -> E.ExprObj (mergeExpr kv newId e2 e)
                False -> E.ExprObj (mergeExpr kv newId e e2)
        in ((changedSyms, ngen), mergedExprObj)

mergeTwoRedirObjs :: KnownValues -> NameGen -> HM.HashMap Id Id -> Id -> E.ExprEnv -> E.ExprEnv -> Name -> Name -> ((HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoRedirObjs kv ngen changedSyms newId eenv1 eenv2 n1 n2 =
        let e1 = case (E.lookup n1 eenv1) of
                    (Just (Var (Id n1' t))) -> Var (Id n1' t)
                    (Just x) -> x
                    Nothing -> error $ "Could not find EnvObj with name: " ++ (show n1)
            e2 = case (E.lookup n2 eenv2) of
                    (Just (Var (Id n2' t))) -> Var (Id n2' t)
                    (Just x) -> x
                    Nothing -> error $ "Could not find EnvObj with name: " ++ (show n2)
            mergedExprObj = E.ExprObj (mergeExpr kv newId e1 e2)
        in ((changedSyms, ngen), mergedExprObj)

mergeTwoSymbObjs :: KnownValues -> NameGen -> HM.HashMap Id Id -> Id -> Id -> Id -> ((HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoSymbObjs kv ngen changedSyms newId i1@(Id _ t1) i2@(Id _ t2) =
        let (newSymId1, ngen') = freshId t1 ngen
            (newSymId2, ngen'') = freshId t2 ngen'
            changedSyms' = HM.insert i2 newSymId2 $ HM.insert i1 newSymId1 changedSyms
            mergedExprObj = E.ExprObj (mergeExpr kv newId (Var newSymId1) (Var newSymId2))
        in ((changedSyms', ngen''), mergedExprObj)

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
        mergedPC = PC.fromList kv common
        mergedPC' = foldr (PC.insert kv) mergedPC (pc1Only' ++ pc2Only')
        mergedPC'' = (PC.insert kv (AssumePC newId 1 (ExtCond (createEqExprInt kv newId 1) True)) mergedPC')
        mergedPC''' = (PC.insert kv (AssumePC newId 2 (ExtCond (createEqExprInt kv newId 2) True)) mergedPC'')
    in mergedPC'''

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
        -- Add the following two expressions to constrain the value newId can take to either 1/2 when solving
        combined_map' = (PC.insert kv (AssumePC newId 1 (ExtCond (createEqExprInt kv newId 1) True)) combined_map) 
        combined_map'' = (PC.insert kv (AssumePC newId 2 (ExtCond (createEqExprInt kv newId 2) True)) combined_map') 
    in foldr (PC.insert kv) combined_map'' newAssumePCs

-- A map and key,value pair are passed as arguments to the function. If the key exists in the map, then both values
-- are combined and the entry deleted from the map. Else the map and value are simply returned as it is.
mergeMapEntries :: Id -> (M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond)
                   -> (Maybe Name)
                   -> (HS.HashSet PC.PathCond, HS.HashSet Name)
                   -> ((M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond), (HS.HashSet PC.PathCond, HS.HashSet Name))
mergeMapEntries newId (pc2_map, newAssumePCs) key (hs1, ns1) =
    case M.lookup key pc2_map of
        Just (hs2, ns2) -> ((pc2_map', newAssumePCs'), (mergedHS, mergedNS))
            where pc2_map' = M.delete key pc2_map
                  (mergedHS, unmergedPCs) = mergeHashSets newId hs1 hs2
                  mergedNS = HS.union ns1 ns2 -- names should still be the same even though some PCs are wrapped in AssumePCs and moved to different node
                  newAssumePCs' = HS.union newAssumePCs unmergedPCs
        Nothing -> ((pc2_map, newAssumePCs), (hs1, ns1))

-- Any PathCond present in both HashSets is added as it is to the new HashSet.
-- A PathCond present in only 1 HashSet is changed to the form 'AssumePC (x == _) PathCond' and added to the new HashSet
mergeHashSets :: Id -> (HS.HashSet PathCond) -> (HS.HashSet PathCond) -> (HS.HashSet PathCond, HS.HashSet PathCond)
mergeHashSets newId hs1 hs2 = (common, unmergedPCs)
    where common = HS.intersection hs1 hs2
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
replaceNonDets :: State t -> State t 
replaceNonDets s@(State {curr_expr = cexpr, expr_env = eenv}) = 
    let eenv' = E.map (replaceNonDetExpr s) eenv
        (CurrExpr eOrR e) = cexpr 
        cexpr' = CurrExpr eOrR (replaceNonDetExpr s e)
    in (s {curr_expr = cexpr', expr_env = eenv'})

replaceNonDetExpr :: State t -> Expr -> Expr
replaceNonDetExpr s (App e1 e2) = App (replaceNonDetExpr s e1) (replaceNonDetExpr s e2)
replaceNonDetExpr s (NonDet (x:xs)) = case x of
    (Assume _ e1 e2) -> if (substAndEval s e1)
                        then (replaceNonDetExpr s e2)
                        else (replaceNonDetExpr s (NonDet xs))
    r -> replaceNonDetExpr s r
replaceNonDetExpr _ (NonDet []) = error "No value in NonDet expr is satisfiable"
replaceNonDetExpr _ e = e

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

-- | Given a NonDet Expr created by merging exprs, replaces it with a symbolic variable. Encodes the choices in the NonDet Expr as Path Constraints
-- Called from evalApp when App center is Prim
replaceNonDetWithSym :: State t -> NameGen -> Expr -> (State t, NameGen, Expr)
replaceNonDetWithSym s@(State {expr_env = eenv, path_conds = pc, known_values = kv, symbolic_ids = syms}) ng e@(NonDet (x:_)) =
    let newSymT = returnType x
        (newSym, ng') = freshId newSymT ng -- create new symbolic variable
        eenv' = E.insertSymbolic (idName newSym) newSym eenv
        syms' = HS.insert newSym syms
        pcs  = createPCs kv e newSym []
        pc' = foldr (PC.insert kv) pc pcs
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
