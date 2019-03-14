module G2.Execution.StateMerging
  ( mergeState
  ) where

import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Primitives
import qualified Data.Text as T

-- todo: check CurrExpr in right form
isMergeable :: Eq t => State t -> State t -> Bool
isMergeable s1 s2 = (exec_stack s1 == exec_stack s2)
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

mergeState :: Eq t => State t -> State t -> Maybe (State t)
mergeState s1 s2 = if isMergeable s1 s2
        then (Just State { 
              expr_env = expr_env s1
             , type_env = type_env s1 -- done
             , curr_expr = curr_expr s1 
             , path_conds = path_conds s1
             , non_red_path_conds = non_red_path_conds s1 -- done
             , true_assert = true_assert s1 -- done
             , assert_ids = assert_ids s1 -- done
             , type_classes = type_classes s1 -- done
             , symbolic_ids = (symbolic_ids s1) ++ (symbolic_ids s2) -- done
             , exec_stack = exec_stack s1 -- done
             , model = model s1 -- done
             , known_values = known_values s1 -- done
             , rules = rules s1 -- done
             , num_steps = num_steps s1 -- done
             , track = track s1 -- done
             , tags = tags s1 }) -- done
        else Nothing

mergeCurrExpr :: KnownValues -> CurrExpr -> CurrExpr -> CurrExpr
mergeCurrExpr kv (CurrExpr Evaluate ce1) (CurrExpr Evaluate ce2) = (CurrExpr Evaluate (mergeExpr kv ce1 ce2))
mergeCurrExpr _ ce1 _  =  ce1 --todo

mergeExpr :: KnownValues -> Expr -> Expr -> Expr
mergeExpr _ (Data dc1) (Data _) = Data dc1
mergeExpr kv (App e1 e2) (App e1' e2') = App (mergeExpr kv e1 e1') (NonDet [Assume Nothing (createEqExpr kv 1) e2, Assume Nothing (createEqExpr kv 2) e2'])
mergeExpr _ e1 _ = e1 -- todo

-- Todo: change 'x' to a name that is guaranteed to not be present? use FreshId/FreshName e.g. src/G2/Initialization/StructuralEq.hs
createEqExpr :: KnownValues -> Integer -> Expr
createEqExpr kv val = let eq = mkEqPrimInt kv
    in App (App eq (Var (Id (Name (T.pack "x") Nothing 0 Nothing) TyLitInt))) (Lit (LitInt val)) 

-- mergeExpr :: Expr -> Expr -> Expr
-- mergeExpr e1 e2 =
--
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

