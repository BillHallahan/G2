{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.LiteralTable 
    ( introduceLitTable
    , inLitTableMode
    , updateLiteralTable
    , getLTArg
    , stopUpdateLastExpl
    , litTableToAllRe
    ) where

import qualified G2.Language.Stack as S
import qualified G2.Language.PathConds as PC
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as E
import G2.Language.Typing
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.Naming
import G2.Language.Expr
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import Data.Maybe

introduceLitTable :: State t -> Name -> Id -> LTUpdate -> State t
introduceLitTable s n i up = s { lit_table_stack = lts
                               , exec_stack = es }
    where lts = S.push lt (lit_table_stack s)
          lt = LitTable { lt_arg = i, lt_mapping = HM.empty }
          es = S.push (LitTableFrame (StartedBuilding n) up) (exec_stack s)

inLitTableMode :: State t -> Bool
inLitTableMode s = let lit_stack = lit_table_stack s
                       non_empty = isJust $ S.pop lit_stack
                   in non_empty

updateLiteralTable :: PathConds -> Expr -> LitTable -> LitTable
updateLiteralTable pcs e lt@(LitTable { lt_mapping = ltm }) = lt { lt_mapping = HM.insert pcs e ltm }

getLTArg :: State t -> Id
getLTArg s = let (table, _) = case S.pop $ lit_table_stack s of
                                  Just x -> x
                                  Nothing -> error "not in literal table mode"
             in lt_arg table

-- When we hit another case frame, the last exploring (or started building)
-- should not update the state when popped, as we only want the `child` nodes
-- of the tree we create on this hacky stack machine to update state
stopUpdateLastExpl :: S.Stack Frame -> S.Stack Frame
stopUpdateLastExpl stck = case S.pop stck of
                              Just ((LitTableFrame (StartedBuilding n) True), rest)
                                  -> S.push (LitTableFrame (StartedBuilding n) False) rest
                              Just ((LitTableFrame (Exploring pcs) True), rest)
                                  -> S.push (LitTableFrame (Exploring pcs) False) rest
                              Just (f, rest) -> S.push f (stopUpdateLastExpl rest)
                              Nothing -> stck

-- We need to make sure the resulting expressions in the lit table only have
-- True or False as possible values. We check for this and add the expression
-- to the PathConds if it isn't True or False, creating two separate versions
-- for each possibility. We also convert all PathConds to their list representation,
-- so that they can be converted to regex more easily.
makeAllBools :: KnownValues -> [(PathConds, Expr)] -> [([PathCond], Bool)]
makeAllBools _ [] = []
makeAllBools kv ((pcs, e):xs) | Just b <- getBool kv e = (PC.toList pcs, b):makeAllBools kv xs
makeAllBools kv ((pcs, e):xs) =
    -- We need two separate additions to the result list: one where the expr is
    -- true and one where it isn't
    let lst = PC.toList pcs
        pc1 = ExtCond e True
        pc2 = ExtCond e False
        lst1 = pc1:lst
        lst2 = pc2:lst
        rest = makeAllBools kv xs
    in (lst1, True):(lst2, False):rest

getBool :: KnownValues -> Expr -> Maybe Bool
getBool kv (Data dc) = getBoolOptFromDC kv dc
getBool _ _ = Nothing

-- Slight duplication from `Rules` but we need a Maybe here
getBoolOptFromDC :: KnownValues -> DataCon -> Maybe Bool
getBoolOptFromDC kv dcon
    | (DataCon dconName dconType [] []) <- dcon
    , dconType == (tyBool kv)
    , dconName == (KV.dcTrue kv) = Just True
    | (DataCon dconName dconType [] []) <- dcon
    , dconType == (tyBool kv)
    , dconName == (KV.dcFalse kv) = Just False
    | otherwise = Nothing

-- We take the `True` path conds, and create a chain of `Or` with them, before using
-- them in `FoldLeft`, (after renaming the variables in the path conditions).
-- This should be the equivalent of
-- `foldl (\prev_bool elem -> prev_bool && lit_table_func elem) True string`
litTableToAllRe :: State t -> NameGen -> LitTable -> Expr -> (StateDiff, NameGen)
litTableToAllRe s ng lt str_e =
    let kv = known_values s
        eenv = expr_env s
        tvnv = tyvar_env s

        lt_lst = HM.toList $ lt_mapping lt
        lt_bools = makeAllBools kv lt_lst
        lt_trues = map fst $ filter snd lt_bools

        (Id lt_arg_name _) = lt_arg lt
        lt_arg_e = fromJust $ E.deepLookup lt_arg_name eenv
        (unboxed_sym, unboxed_name) =
            case lt_arg_e of
                App _ (v@(Var i)) -> (v, idName i)
                _ -> error $ "lit table arg not in form (data_con unboxed_sym): " ++ show lt_arg_e

        -- Not entirely sure if the element variable should be unboxed or not
        lit_ty = typeOf tvnv unboxed_sym
        (accum_var, ng1) = freshId (tyBool kv) ng
        (elem_var, ng2) = freshId lit_ty ng1

        -- No path conds means any input is true, otherwise we need one path cond to be true
        or_exp = if null lt_lst then mkTrue kv
                 else case L.uncons lt_trues of
                    Nothing -> mkFalse kv
                    Just (hd, tl) -> L.foldl' (\prev_exp pcs -> mkApp [Prim Or (tyBool kv), prev_exp, pcsToExpr kv pcs]) (pcsToExpr kv hd) tl

        or_exp1 = replaceVar unboxed_name (Var elem_var) or_exp
        and_exp = mkApp [Prim And (tyBool kv), Var accum_var, or_exp1]
        fun_exp = Lam TermL accum_var (Lam TermL elem_var and_exp)
        fun_ty = mkTyFun [mkTyFun [tyBool kv, lit_ty, tyBool kv], tyBool kv, typeOf tvnv str_e, tyBool kv]
        fold_exp = mkApp [Prim FoldLeft fun_ty, fun_exp, mkTrue kv, str_e]
    in
    (SD { new_conc_entries = [], new_sym_entries = [accum_var, elem_var]
        , new_path_conds = [], concretized = []
        , new_true_assert = true_assert s, new_assert_ids = assert_ids s
        , new_curr_expr = CurrExpr Return fold_exp
        , new_conc_types = [], new_sym_types = [], new_mut_vars = [] }, ng2)

-- Turn the conjunction of these path conditions into an expression
pcsToExpr :: KnownValues -> [PathCond] -> Expr
pcsToExpr kv pcs =
    case L.uncons pcs of
        Nothing -> mkTrue kv
        Just (hd, tl) -> L.foldl' (\prev_exp pc -> mkApp [Prim And (tyBool kv), prev_exp, pcToExpr kv pc]) (pcToExpr kv hd) tl

-- Turn one path condition into an expression, with equality
pcToExpr :: KnownValues -> PathCond -> Expr
pcToExpr kv pc =
    case pc of
        ExtCond expr bool -> if bool then expr else mkApp [Prim Not (tyBool kv), expr]
        AltCond lit var bool -> let eq_e = mkApp [Prim Eq (tyBool kv), Lit lit, var]
                                in if bool then eq_e else mkApp [Prim Not (tyBool kv), eq_e]
        _ -> error $ "unhandled pc:\n" ++ show pc
