module G2.Execution.NormalForms where

import G2.Language
import qualified G2.Language.Stack as S
import qualified G2.Language.ExprEnv as E
import qualified G2.Execution.MergingHelpers as SM

-- | If something is in "value form", then it is essentially ready to be
-- returned and popped off the heap. This will be the SSTG equivalent of having
-- Return vs Evaluate for the ExecCode of the `State`.
--
-- So in this context, the following are considered NOT-value forms:
--   `Var`, only if a lookup still available in the expression environment.
--   `App`, which involves pushing the RHS onto the `Stack`, if the center is not a Prim or DataCon
--   `Let`, which involves binding the binds into the eenv
--   `Case`, which involves pattern decomposition and stuff.
isExprValueForm :: E.ExprEnv -> Expr -> Bool
isExprValueForm eenv (Var var) =
    E.lookup (idName var) eenv == Nothing || E.isSymbolic (idName var) eenv
isExprValueForm eenv (App f a) = case unApp (App f a) of
    (Prim _ _:xs) -> all (isExprValueForm eenv) xs
    (Data _:_) -> True
    ((Var _):_) -> False
    _ -> False
isExprValueForm _ (Let _ _) = False
isExprValueForm _ (Case _ _ _) = False
isExprValueForm eenv (Cast e (t :~ _)) = not (hasFuncType t) && isExprValueForm eenv e
isExprValueForm _ (Tick _ _) = False
isExprValueForm _ (NonDet _) = False
isExprValueForm _ (SymGen _) = False
isExprValueForm _ (Assume _ _ _) = False
isExprValueForm _ (Assert _ _ _) = False
isExprValueForm _ _ = True

-- | Is the execution state in a value form of some sort? This would entail:
-- * The `Stack` is empty.
-- * The `ExecCode` is in a `Return` form.
-- * We have no path conds to reduce
isExecValueForm :: State t -> Bool
isExecValueForm state | Nothing <- S.pop (exec_stack state)
                      , CurrExpr Return _ <- curr_expr state
                      , non_red_path_conds state == [] = True
                      | otherwise = False


isExecValueFormDisNonRedPC :: State t -> Bool
isExecValueFormDisNonRedPC s = isExecValueForm $ s {non_red_path_conds = []}

isSymMergedNormalForm :: E.ExprEnv -> Expr -> Bool
isSymMergedNormalForm eenv (NonDet xs) = all (isSymMergedNormalForm' eenv) xs
isSymMergedNormalForm eenv e = isExprValueForm eenv e

isSymMergedNormalForm' :: E.ExprEnv -> Expr -> Bool
isSymMergedNormalForm' eenv (Assume _ e1 e2) = isSymMergedNormalForm eenv e2 && (SM.isSMAssumption e1)
isSymMergedNormalForm' _ _ = False

