module G2.Execution.StateMerging
  ( mergeState
  , mergeCurrExpr
  , createEqExpr
  , replaceNonDets
  , mergeExpr
  , mergeExprEnv
  , mergeEnvObj
  , mergePathConds
  ) where

import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Primitives
import G2.Language.Naming
import G2.Language.TypeClasses
import G2.Language.Expr
import G2.Execution.PrimitiveEval
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.HashSet as HS
import qualified Data.List as L

isMergeable :: Eq t => State t -> State t -> Bool
isMergeable s1 s2 = 
    (exec_stack s1 == exec_stack s2)
    && (isMergeableCurrExpr (curr_expr s1) (curr_expr s2))
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

mergeState :: Eq t => NameGen -> State t -> State t -> (NameGen, Maybe (State t))
mergeState ngen s1 s2 = 
    if isMergeable s1 s2
        then 
            let (newId, ngen') = freshId TyLitInt ngen
                curr_expr' = mergeCurrExpr (known_values s1) newId (curr_expr s1) (curr_expr s2) 
                syms' = (symbolic_ids s1) ++ (symbolic_ids s2) ++ [newId]
                (expr_env', (syms'', ngen'')) = mergeExprEnv (known_values s1) newId syms' ngen' (expr_env s1) (expr_env s2)
                path_conds' = mergePathConds (known_values s1) newId (path_conds s1) (path_conds s2)
            in (ngen''
               , (Just State { expr_env = expr_env'
                             , type_env = type_env s1
                             , curr_expr = curr_expr'
                             , path_conds = path_conds'
                             , non_red_path_conds = non_red_path_conds s1
                             , true_assert = true_assert s1
                             , assert_ids = assert_ids s1
                             , type_classes = type_classes s1
                             , symbolic_ids = syms''
                             , exec_stack = exec_stack s1
                             , model = model s1
                             , known_values = known_values s1
                             , rules = rules s1
                             , num_steps = num_steps s1
                             , track = track s1
                             , tags = tags s1 }))
        else (ngen, Nothing)

isMergeableCurrExpr :: CurrExpr -> CurrExpr -> Bool
isMergeableCurrExpr (CurrExpr Evaluate ce1) (CurrExpr Evaluate ce2) = isMergeableExpr ce1 ce2
isMergeableCurrExpr (CurrExpr Return ce1) (CurrExpr Return ce2) = isMergeableExpr ce1 ce2
isMergeableCurrExpr _ _ = False

-- Returns True if both Exprs are of the form (App ... (Data DataCon) ....) and contain the same Data Constructor
isMergeableExpr :: Expr -> Expr -> Bool
isMergeableExpr (App e1 _) (App e1' _) = isMergeableExpr e1 e1' 
isMergeableExpr (Data dc1) (Data dc2) = dc1 == dc2
isMergeableExpr _ _ = False

mergeCurrExpr :: KnownValues -> Id -> CurrExpr -> CurrExpr -> CurrExpr
mergeCurrExpr kv newId (CurrExpr evalOrRet ce1) (CurrExpr evalOrRet2 ce2)
    | evalOrRet == evalOrRet2 = (CurrExpr evalOrRet mergedExpr)
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."
        where 
            mergedExpr = mergeExpr kv newId ce1 ce2

-- | Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D NonDet[(Assume (x == 1) in e_1), (Assume (x == 2) in e_1')],..., NonDet[(Assume (x == 1) in e_n), (Assume (x == 2) in e_n')]" 
mergeExpr :: KnownValues -> Id -> Expr -> Expr -> Expr
mergeExpr kv newId (App e1 e2) (App e1' e2') = App (mergeExpr kv newId e1 e1') (mergeExpr' kv newId e2 e2')
mergeExpr _ _ (Data dc) (Data dc') = if dc == dc' then (Data dc) else error "Exprs to be merged have different underlying DataCons."
mergeExpr _ _ _ _ = error $ "Exprs to be merged have an invalid form."

-- | Helper function to merge outer arguments of Exprs being merged in mergeExpr
mergeExpr' :: KnownValues -> Id -> Expr -> Expr -> Expr
mergeExpr' kv newId (App e1 e2) (App e1' e2') = App (mergeExpr' kv newId e1 e1') (mergeExpr' kv newId e2 e2')
mergeExpr' kv newId e1 e1' = if (e1 == e1') 
    then e1
    else NonDet [Assume Nothing (createEqExpr kv newId 1) e1, Assume Nothing (createEqExpr kv newId 2) e1']

-- | Returns an Expr equivalent to "x == val", where x is a Var created from the given Id
createEqExpr :: KnownValues -> Id -> Integer -> Expr
createEqExpr kv newId val = App (App eq (Var newId)) (Lit (LitInt val)) 
    where eq = mkEqPrimInt kv

-- | Keeps all EnvObjs found in only one ExprEnv, and combines the common (key, value) pairs using the mergeEnvObj function
mergeExprEnv :: KnownValues -> Id -> SymbolicIds -> NameGen -> E.ExprEnv -> E.ExprEnv -> (E.ExprEnv, (SymbolicIds, NameGen))
mergeExprEnv kv newId syms ngen eenv1 eenv2 = (E.wrapExprEnv $ M.unions [merged_map', eenv1_rem, eenv2_rem], (syms'++newSyms, ngen'))
    where eenv1_map = E.unwrapExprEnv eenv1
          eenv2_map = E.unwrapExprEnv eenv2
          zipped_maps = (M.intersectionWith (\a b -> (a,b)) eenv1_map eenv2_map)
          ((newSyms, syms', ngen'), merged_map) = M.mapAccum (mergeEnvObj kv newId eenv1 eenv2) ([], syms, ngen) zipped_maps
          merged_map' = foldr (\i@(Id n _) m -> M.insert n (E.SymbObj i) m) merged_map newSyms
          eenv1_rem = (M.difference eenv1_map eenv2_map)
          eenv2_rem = (M.difference eenv2_map eenv1_map)

-- | If both arguments are ExprObjs, the first ExprObj is returned if they are equal, else they are combined using mergeExpr
-- Else, function checks if both EnvObjs are equal and returns the first
mergeEnvObj :: KnownValues -> Id
               -> E.ExprEnv
               -> E.ExprEnv
               -> (SymbolicIds, SymbolicIds, NameGen)
               -> (E.EnvObj, E.EnvObj)
               -> ((SymbolicIds, SymbolicIds, NameGen), E.EnvObj)
mergeEnvObj kv newId eenv1 eenv2 (newSyms, syms, ngen) (eObj1, eObj2)
    | (E.ExprObj e1) <- eObj1
    , (E.ExprObj e2) <- eObj2 =
        if (e1 == e2)
            then ((newSyms, syms, ngen), eObj1)
            else ((newSyms, syms, ngen), E.ExprObj (mergeExpr' kv newId e1 e2))
    -- replace the Id in the SymbObj with a new symbolic variable and combine with the expr in the ExprObj in a NonDet expr
    | (E.SymbObj i@(Id _ t)) <- eObj1
    , (E.ExprObj e2) <- eObj2 =
        let (newSymId, ngen') = freshId t ngen
            newSyms' = newSymId:newSyms
            syms' = L.filter (/= i) syms
        in ((newSyms', syms', ngen'), E.ExprObj (mergeExpr' kv newId (Var newSymId) e2))
    | (E.ExprObj e1) <- eObj1
    , (E.SymbObj i@(Id _ t)) <- eObj2 =
        let (newSymId, ngen') = freshId t ngen
            newSyms' = newSymId:newSyms
            syms' = L.filter (/= i) syms
        in ((newSyms', syms', ngen'), E.ExprObj (mergeExpr' kv newId e1 (Var newSymId)))
    | (E.SymbObj i1@(Id _ t1)) <- eObj1
    , (E.SymbObj i2@(Id _ t2)) <- eObj2
    , i1 /= i2 =
        let (newSymId1, ngen') = freshId t1 ngen
            (newSymId2, ngen'') = freshId t2 ngen'
            newSyms' = newSymId1:newSymId2:newSyms
            syms' = L.filter (\x -> (x /= i2) &&  (x /= i1)) syms
        in ((newSyms', syms', ngen''), E.ExprObj (mergeExpr' kv newId (Var newSymId1) (Var newSymId2)))
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj e2) <- eObj2 =
        let e1 = E.lookup n eenv1
        in case e1 of
            (Just (Var (Id _ t))) -> ((newSyms, syms, ngen), E.ExprObj (mergeExpr' kv newId (Var (Id n t)) e2))
            (Just e1') -> ((newSyms, syms, ngen), E.ExprObj (mergeExpr' kv newId e1' e2))
            Nothing -> error $ "Could not find EnvObj that RedirObj: " ++ (show eObj1) ++ " points to."
    | (E.ExprObj e1) <- eObj1
    , (E.RedirObj n) <- eObj2 =
        let e2 = E.lookup n eenv2
        in case e2 of
            (Just (Var (Id _ t))) -> ((newSyms, syms, ngen), E.ExprObj (mergeExpr' kv newId e1 (Var (Id n t))))
            (Just e2') -> ((newSyms, syms, ngen), E.ExprObj (mergeExpr' kv newId e1 e2'))
            Nothing -> error $ "Could not find EnvObj that RedirObj: " ++ (show eObj2) ++ " points to."
    | otherwise =
        if (eObj1 == eObj2)
            then ((newSyms, syms, ngen), eObj1)
            else error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

mergePathConds :: KnownValues -> Id -> PathConds -> PathConds -> PathConds
mergePathConds kv newId pc1 pc2 = 
    -- If a key exists in both maps, then the respective values are combined and inserted into pc1_map'. 
    -- Else, all other values in pc1_map are added to pc1_map' as it is.
    -- pc2_map' will only contain values whose keys are not present in pc1_map
    let
        (pc2_map', pc1_map') = M.mapAccumWithKey (mergeMapEntries newId) pc2_map pc1_map
        pc2_map = PC.toMap pc2
        pc1_map = PC.toMap pc1
        combined_map = PC.PathConds (M.union pc2_map' pc1_map')
        -- Add the following two expressions to constrain the value newId can take to either 1/2 when solving
        combined_map' = (PC.insert kv (AssumePC newId 1 (ExtCond (createEqExpr kv newId 1) True)) combined_map) 
        combined_map'' = (PC.insert kv (AssumePC newId 2 (ExtCond (createEqExpr kv newId 2) True)) combined_map') 
    in combined_map''

-- A map and key,value pair are passed as arguments to the function. If the key exists in the map, then both values
-- are combined and the entry deleted from the map. Else the map and value are simply returned as it is.
mergeMapEntries :: Id -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name])) -> (Maybe Name) ->
                   (HS.HashSet PC.PathCond, [Name]) -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]), (HS.HashSet PC.PathCond, [Name]))
mergeMapEntries newId pc2_map key (hs1, ns1) =
    case M.lookup key pc2_map of
        Just (hs2, ns2) -> (pc2_map', (mergedHS, mergedNS))
            where pc2_map' = M.delete key pc2_map
                  (mergedHS, addNewIdName) = mergeHashSets newId hs1 hs2
                  mergedNS = L.nub $ if addNewIdName then (idName newId):(ns1 ++ ns2) else (ns1 ++ ns2)
        Nothing -> (pc2_map, (hs1, ns1))

-- Any PathCond present in both HashSets is added as it is to the new HashSet.
-- A PathCond present in only 1 HashSet is changed to the form 'AssumePC (x == _) PathCond' and added to the new HashSet
mergeHashSets :: Id -> (HS.HashSet PathCond) -> (HS.HashSet PathCond) -> (HS.HashSet PathCond, Bool)
mergeHashSets newId hs1 hs2 = (HS.union (HS.union common hs1') hs2', addNewIdName)
    where common = HS.intersection hs1 hs2
          hs1Minus2 = HS.difference hs1 hs2
          hs2Minus1 = HS.difference hs2 hs1
          addNewIdName = not $ ((HS.null hs1Minus2) && (HS.null hs2Minus1)) -- True if we need to add name of newId to list of names in node
          hs1' = HS.map (\pc -> AssumePC newId 1 pc) hs1Minus2
          hs2' = HS.map (\pc -> AssumePC newId 2 pc) hs2Minus1

-- removes any NonDets in ExprObjs, leaves SymbObjs (and RedirObjs) intact since replaceNonDetExpr doesn't change Exprs of type (Var _ _)
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

substAndEval :: State t -> Expr -> Bool
substAndEval (State {model = m
                      , known_values = kv
                      , type_env = tenv
                      , type_classes = tc}) e = 
    getBoolFromDataCon kv solvedExpr 
    where
        exprToSolve = subExpr m tc e
        solvedExpr = evalPrim kv tenv exprToSolve

subExpr :: Model -> TypeClasses -> Expr -> Expr
subExpr m tc = modifyContainedASTs (subExpr' m tc [])

subExpr' :: Model -> TypeClasses -> [Id] -> Expr -> Expr
subExpr' m tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- M.lookup n m =
        subExpr' m tc (i:is) e
    | otherwise = v
subExpr' m tc is e = modifyChildren (subExpr' m tc is) e
