{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.LiteralTable
    ( introduceLitTable
    , inLitTableMode
    , updateLiteralTable
    , getLTArg
    , stopUpdateLastExpl
    , litTableToLam
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
          lt = LitTable { lt_arg = i
                        , lt_mapping = HM.empty
                        , lt_errored = False
                        , lt_init_pcs = path_conds s
                        }
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
-- True as possible values. We check for this and add the expression
-- to the PathConds if it is True, or if it is an expression we can make True
makeAllTrue :: KnownValues -> [(PathConds, Expr)] -> [[PathCond]]
makeAllTrue _ [] = []
makeAllTrue kv ((pcs, e):xs) | Just True <- getBool kv e = (PC.toList pcs):makeAllTrue kv xs
makeAllTrue kv ((pcs, e):xs) =
    let lst = PC.toList pcs
        pc1 = ExtCond e True
        lst1 = pc1:lst
        rest = makeAllTrue kv xs
    in lst1:rest

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

-- The identity function represented as a `Lam`
mkIdLam :: State t -> NameGen -> LitTable -> (Expr, EESymDiff, NameGen)
mkIdLam s ng lt =
    let tvnv = tyvar_env s
        kv = known_values s
        tenv = type_env s
        arg_ty = typeOf tvnv $ lt_arg lt
        (arg_id, ng1) = freshId arg_ty ng
        lam_e = Lam TermL arg_id (Var arg_id)
        tup_e = mkTup kv tenv tvnv lam_e $ mkTrue kv
    in (tup_e, [arg_id], ng1)

-- Return Id for argument, and the Name that we're replacing in path conds
mkLamArg :: State t -> NameGen -> LitTable -> (Id, Name, NameGen)
mkLamArg s ng lt =
    let eenv = expr_env s
        tvnv = tyvar_env s

        (Id lt_arg_name _) = lt_arg lt
        lt_arg_e = fromJust $ E.deepLookup lt_arg_name eenv
        (unboxed_sym, unboxed_name) =
            case lt_arg_e of
                App _ (v@(Var i)) -> (v, idName i)
                _ -> error $ "lit table arg not in form (data_con unboxed_sym): " ++ show lt_arg_e

        -- Not entirely sure if the element variable should be unboxed or not
        lit_ty = typeOf tvnv unboxed_sym
        (elem_var, ng1) = freshId lit_ty ng
    in (elem_var, unboxed_name, ng1)

-- Make a fully applied primitive tuple
mkTup :: KnownValues -> TypeEnv -> TyVarEnv -> Expr -> Expr -> Expr
mkTup kv tenv tv_env x y =
    mkApp [ mkPrimTuple kv tenv
          , Type TyUnknown
          , Type TyUnknown
          , Type $ typeOf tv_env x
          , Type $ typeOf tv_env y
          , x
          , y
          ]

-- Convert the literal table to a lambda function, which is then returned
-- For functions returning a boolean, we optimize the representation to be
-- the disjunction of all True path conditions (using `Prim Or`).
-- For other functions, we use `ite`.
litTableToLam :: State t -> NameGen -> LitTable -> (Expr, EESymDiff, NameGen)
litTableToLam s ng lt =
    if lt_errored lt then
        (mkTup kv tenv tv_env (Prim UnspecifiedOutput TyUnknown) (mkFalse kv), [], ng)
    else
        case HM.toList $ lt_mapping lt of
            [] ->
                mkIdLam s ng lt
            ((_, e):_) | typeOf tv_env e == tyBool kv ->
                litTableToLamBool s ng lt
            _ ->
                litTableToLamNonBool s ng lt
    where
        kv = known_values s
        tenv = type_env s
        tv_env = tyvar_env s

litTableToLamBool :: State t -> NameGen -> LitTable -> (Expr, EESymDiff, NameGen)
litTableToLamBool s ng lt =
    let kv = known_values s
        tenv = type_env s
        tv_env = tyvar_env s
        (elem_var, unboxed_name, ng1) = mkLamArg s ng lt

        lt_lst = HM.toList $ lt_mapping lt
        lt_trues = makeAllTrue kv lt_lst

        -- At this point, we know the literal table is non-empty, since we are creating a lambda for
        -- a boolean-returning function
        or_exp = case lt_trues of
                    [] -> mkFalse kv
                    (hd:tl) ->
                        L.foldl'
                            (\prev_exp pcs -> mkApp [Prim Or (tripleBoolTy kv), prev_exp, pcsToExprBool kv pcs])
                            (pcsToExprBool kv hd)
                            tl

        or_exp1 = replaceVar unboxed_name (Var elem_var) or_exp
        fun_exp = Lam TermL elem_var or_exp1
        tup_exp = mkTup kv tenv tv_env fun_exp $ mkTrue kv
    in (tup_exp, [elem_var], ng1)

-- Turn the conjunction of these path conditions into an expression
pcsToExprBool :: KnownValues -> [PathCond] -> Expr
pcsToExprBool kv pcs =
    case pcs of
        [] -> mkTrue kv
        (hd:tl) ->
            L.foldl' (\prev_exp pc -> mkApp [Prim And (tripleBoolTy kv), prev_exp, pcToExprBool kv pc]) (pcToExprBool kv hd) tl

-- Turn one path condition into an expression, with equality
pcToExprBool :: KnownValues -> PathCond -> Expr
pcToExprBool kv pc =
    case pc of
        ExtCond expr bool -> if bool then expr else mkApp [Prim Not (doubleBoolTy kv), expr]
        AltCond lit var bool -> let eq_e = mkApp [Prim Eq (tripleBoolTy kv), Lit lit, var]
                                in if bool then eq_e else mkApp [Prim Not (doubleBoolTy kv), eq_e]
        _ -> error $ "unhandled pc:\n" ++ show pc

litTableToLamNonBool :: State t -> NameGen -> LitTable -> (Expr, EESymDiff, NameGen)
litTableToLamNonBool s ng lt =
    let (elem_var, unboxed_name, ng1) = mkLamArg s ng lt
        kv = known_values s
        tv_env = tyvar_env s
        tenv = type_env s
        lt_lst = HM.toList $ lt_mapping lt
        -- `Char`s are represented as one character `String`s here, so we
        -- need to extract the first character.
        wrap e t = if t == tyChar kv
                       then mkApp [Prim SeqNth TyUnknown, e, Lit $ LitInt 0]
                       else e
        -- At this point, we assume there are no `Error`s in the literal table. This
        -- means we have a total function, and we can pick one option to be the default.
        ite_exp = case lt_lst of
                    ((_ {- We ignore the PathConds for the default -}, def_e):rest) ->
                        L.foldl'
                            (\prev_exp (pcs, e) ->
                                mkApp [ Prim Ite TyUnknown
                                      , (pcsToExprBool kv $ PC.toList pcs)
                                      , (wrap e $ typeOf tv_env e)
                                      , prev_exp]
                            )
                            (wrap def_e $ typeOf tv_env def_e)
                            (reverse rest)
                    _ -> error "impossible, empty list despite checking in litTableToLam"
        ite_exp1 = replaceVar unboxed_name (Var elem_var) ite_exp
        fun_exp = Lam TermL elem_var ite_exp1
        tup_exp = mkTup kv tenv tv_env fun_exp $ mkTrue kv
    in (tup_exp, [elem_var], ng1)

tripleBoolTy :: KnownValues -> Type
tripleBoolTy kv = mkTyFun [tyBool kv, tyBool kv, tyBool kv]

doubleBoolTy :: KnownValues -> Type
doubleBoolTy kv = mkTyFun [tyBool kv, tyBool kv]
