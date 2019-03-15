module G2.Execution.StateMerging
  ( mergeState
  ) where

import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Primitives
import G2.Language.Naming
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.HashSet as HS
import qualified Data.List as L

isMergeable :: Eq t => State t -> State t -> Bool
isMergeable s1 s2 = 
    (exec_stack s1 == exec_stack s2)
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
                expr_env' = mergeExprEnv (known_values s1) newId (expr_env s1) (expr_env s2)
                path_conds' = mergePathConds (known_values s1) newId (path_conds s1) (path_conds s2)
            in (ngen'
               , (Just State { expr_env = expr_env'
                             , type_env = type_env s1
                             , curr_expr = curr_expr'
                             , path_conds = path_conds'
                             , non_red_path_conds = non_red_path_conds s1
                             , true_assert = true_assert s1
                             , assert_ids = assert_ids s1
                             , type_classes = type_classes s1
                             , symbolic_ids = (symbolic_ids s1) ++ (symbolic_ids s2)
                             , exec_stack = exec_stack s1
                             , model = model s1
                             , known_values = known_values s1
                             , rules = rules s1
                             , num_steps = num_steps s1
                             , track = track s1
                             , tags = tags s1 }))
        else (ngen, Nothing)

mergeCurrExpr :: KnownValues -> Id -> CurrExpr -> CurrExpr -> CurrExpr
mergeCurrExpr kv newId (CurrExpr Evaluate ce1) (CurrExpr Evaluate ce2) = (CurrExpr Evaluate mergedExpr)
    where mergedExpr = mergeExpr kv newId ce1 ce2
mergeCurrExpr _ _ ce1 _  =  ce1

-- Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D NonDet[(Assume (x == 1) in e_1), (Assume (x == 2) in e_1')],..., NonDet[(Assume (x == 1) in e_n), (Assume (x == 2) in e_n')]" 
mergeExpr :: KnownValues -> Id -> Expr -> Expr -> Expr
mergeExpr _ _ (Data dc1) (Data _) = Data dc1
mergeExpr kv newId (App e1 e2) (App e1' e2') = 
    App (mergeExpr kv newId e1 e1') (NonDet [Assume Nothing (createEqExpr kv newId 1) e2, Assume Nothing (createEqExpr kv newId 2) e2'])
mergeExpr _ _ e1 _ = e1 -- todo

-- Returns an Expr equivalent to "x == val", where x is a Var created from the given Id
createEqExpr :: KnownValues -> Id -> Integer -> Expr
createEqExpr kv newId val = App (App eq (Var newId)) (Lit (LitInt val)) 
    where eq = mkEqPrimInt kv

-- For example (todo: delete):
-- (... (App (App (Data (DataCon Name Type)) 
--           (NonDet [
--              (Assume Nothing (App (App (Prim Eq (TyFun TyLitInt (TyFun TyLitInt (TyCon (Name "Bool" (Just "GHC.Types") 0 Nothing) TYPE)))) (Var (Id (Name "x" Nothing 1234 Nothing) TyLitInt))) (Lit (LitInt 1))) Expr1), 
--              (Assume Nothing (App (App (Prim Eq (TyFun TyLitInt (TyFun TyLitInt (TyCon (Name "Bool" (Just "GHC.Types") 0 Nothing) TYPE)))) (Var (Id (Name "x" Nothing 1234 Nothing) TyLitInt))) (Lit (LitInt 2))) Expr1')
--           ])) 
--      (NonDet [
--          (Assume Nothing (App (App (Prim Eq (TyFun TyLitInt (TyFun TyLitInt (TyCon (Name "Bool" (Just "GHC.Types") 0 Nothing) TYPE)))) (Var (Id (Name "x" Nothing 1234 Nothing) TyLitInt))) (Lit (LitInt 1))) Expr2), 
--          (Assume Nothing (App (App (Prim Eq (TyFun TyLitInt (TyFun TyLitInt (TyCon (Name "Bool" (Just "GHC.Types") 0 Nothing) TYPE)))) (Var (Id (Name "x" Nothing 1234 Nothing) TyLitInt))) (Lit (LitInt 1))) Expr2')
--          ])
--      ) 
--  ... )

-- Keeps all EnvObjs found in only one ExprEnv, and combines the common (key, value) pairs using the mergeEnvObj function
mergeExprEnv :: KnownValues -> Id -> E.ExprEnv -> E.ExprEnv -> E.ExprEnv
mergeExprEnv kv newId eenv1 eenv2 = E.wrapExprEnv $ M.unions [merged_map, eenv1_rem, eenv2_rem]
    where merged_map = (M.intersectionWith (mergeEnvObj kv newId) eenv1_map eenv2_map)
          eenv1_rem = (M.difference eenv1_map eenv2_map)
          eenv2_rem = (M.difference eenv2_map eenv1_map)
          eenv1_map = E.unwrapExprEnv eenv1
          eenv2_map = E.unwrapExprEnv eenv2

-- If both arguments are ExprObjs, in the case they are equal, the first ExprObj is returned, else they are combined using mergeExpr
-- Else, function assumes both EnvObjs must be equal and returns the first
mergeEnvObj :: KnownValues -> Id -> E.EnvObj -> E.EnvObj -> E.EnvObj
mergeEnvObj kv newId val1@(E.ExprObj expr1) (E.ExprObj expr2) = 
    if (expr1 == expr2)
        then val1
        else E.ExprObj (mergeExpr kv newId expr1 expr2)
mergeEnvObj _ _ val1 _ = val1

-- (todo: delete comment)
-- for each name in pc1:
--      lookup name in pc2
--      if name in pc2:
--          merge both hashsets:
--             intersection of both 
--             + difference HashSet 1 HashSet 2
--                  where each elem is modified to: AssumePC (x == 1) pc
--             + difference HashSet 2 HashSet 1
--                  where each elem is modified to: AssumePC (x == 2) pc
--          merge names
--          delete name from pc2
--          add (merged HashSet, merged [Name]) new map
--      else:
--          add entry to new map
-- for each remaining name in pc2:
--      add to new map

mergePathConds :: KnownValues -> Id -> PathConds -> PathConds -> PathConds
mergePathConds kv newId pc1 pc2 = PC.PathConds (M.union pc2_map' pc1_map')
    -- If a key exists in both maps, then the respective values are combined and inserted into pc1_map'. 
    -- Else, the value is added to pc1_map' as it is.
    -- pc2_map' will only contain values whose keys are not present in pc1_map
    where (pc2_map', pc1_map') = M.mapAccumWithKey (mergeMapEntries kv newId) pc2_map pc1_map 
          pc2_map = PC.toMap pc2
          pc1_map = PC.toMap pc1

-- A map and key,value pair are passed as arguments to the function. If the key exists in the map, then both values
-- are combined and the entry deleted from the map. Else the map and value are simply returned as it is.
mergeMapEntries :: KnownValues -> Id -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name])) -> (Maybe Name) -> 
                   (HS.HashSet PC.PathCond, [Name]) -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]), (HS.HashSet PC.PathCond, [Name]))
mergeMapEntries kv newId pc2_map key (hs1, ns1) = 
    case M.lookup key pc2_map of
        Just (hs2, ns2) -> (pc2_map', (mergeHashSets kv newId hs1 hs2, L.nub $ ns1 ++ ns2))
            where pc2_map' = M.delete key pc2_map
        Nothing -> (pc2_map, (hs1, ns1))

mergeHashSets :: KnownValues -> Id -> (HS.HashSet PathCond) -> (HS.HashSet PathCond) -> (HS.HashSet PathCond)
mergeHashSets kv newId hs1 hs2 = HS.union (HS.union common hs1') hs2'
    where common = HS.intersection hs1 hs2
          hs1' = HS.map (\pc -> AssumePC (createEqExpr kv newId 1) pc) (HS.difference hs1 hs2)
          hs2' = HS.map (\pc -> AssumePC (createEqExpr kv newId 2) pc) (HS.difference hs2 hs1)



