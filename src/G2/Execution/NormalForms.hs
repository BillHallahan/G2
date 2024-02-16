module G2.Execution.NormalForms where

import G2.Language
import qualified G2.Language.Stack as S
import qualified G2.Language.ExprEnv as E
import G2.Language.Typing

import qualified Data.HashSet as HS

-- A Var counts as being in EVF if it's symbolic or if it's unmapped.
isSWHNF :: State t -> Bool
isSWHNF (State { expr_env = h, curr_expr = CurrExpr _ e }) =
  let e' = modifyASTs stripTicks e
      t = typeOf e'
  in case e' of
    Var _ -> (isPrimType t || not (concretizable t)) && isExprValueForm h e'
    _ -> isExprValueForm h e'

stripTicks :: Expr -> Expr
stripTicks (Tick _ e) = e
stripTicks e = e

-- used by EquivADT and Tactics
concretizable :: Type -> Bool
concretizable (TyVar _) = False
concretizable (TyForAll _ _) = False
concretizable (TyFun _ _) = False
concretizable t@(TyApp _ _) =
  concretizable $ last $ unTyApp t
concretizable TYPE = False
concretizable TyUnknown = False
concretizable _ = True

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
isExprValueForm _ (Case _ _ _ _) = False
isExprValueForm eenv (Cast e (t :~ _)) = not (hasFuncType t) && isExprValueForm eenv e
isExprValueForm _ (Tick _ _) = False
isExprValueForm _ (NonDet _) = False
isExprValueForm _ (SymGen _ _) = False
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

normalForm :: E.ExprEnv -> Expr -> Bool
normalForm = normalForm' HS.empty

normalForm' :: HS.HashSet Name -> E.ExprEnv -> Expr -> Bool
normalForm' looked eenv (Var (Id n _))
    | n `HS.member` looked = True
    | Just e <- E.lookup n eenv = normalForm' (HS.insert n looked) eenv e
    | otherwise = E.isSymbolic n eenv
normalForm' looked eenv (App f a) = case unApp (App f a) of
    (Prim _ _:xs) -> all (normalForm' looked eenv) xs
    (Data _:xs) -> all (normalForm' looked eenv) xs
    ((Var _):_) -> False
    _ -> False
normalForm' _ _ (Let _ _) = False
normalForm' _ _ (Case _ _ _ _) = False
normalForm' looked eenv (Cast e (t :~ _)) = not (hasFuncType t) && normalForm' looked eenv e
normalForm' _ _ (Tick _ _) = False
normalForm' _ _ (NonDet _) = False
normalForm' _ _ (SymGen _ _) = False
normalForm' _ _ (Assume _ _ _) = False
normalForm' _ _ (Assert _ _ _) = False
normalForm' _ _ _ = True
