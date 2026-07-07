{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.LiteralTable
    ( introduceLitTable
    , inLitTableMode
    , updateLiteralTable
    , getLTArg
    , stopUpdateLastExpl
    , litTableToLam
    , splitStateLT
    ) where

import qualified G2.Language.Stack as S
import qualified G2.Language.PathConds as PC
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.CallGraph as CG
import G2.Language.Typing
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.Naming
import G2.Language.Expr
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.List as L
import Data.Maybe

introduceLitTable :: State t -> Name -> Id -> Type -> State t
introduceLitTable s n i t = s { lit_table_stack = lts
                              , exec_stack = es
                              }
    where lts = S.push lt (lit_table_stack s)
          lt = LitTable { lt_arg = i
                        , lt_rec_funs = HS.empty
                        , lt_mapping = HM.empty
                        , lt_errored = False
                        , lt_init_pcs = path_conds s
                        , lt_partial = False
                        , lt_ret_ty = t
                        }
          es = S.push (LitTableFrame (StartedBuilding n) True) (exec_stack s)

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
mkIdLam :: State t -> NameGen -> LitTable -> Maybe (Expr, EESymDiff, NameGen)
mkIdLam s ng lt =
    let tvnv = tyvar_env s
        kv = known_values s
        tenv = type_env s
        arg_ty = typeOf tvnv $ lt_arg lt
        ret_ty = lt_ret_ty lt
        (arg_id, ng1) = freshId arg_ty ng
        lam_e = Lam TermL arg_id (Var arg_id)
        tup_e = mkTup4 kv tenv tvnv
                    lam_e
                    (mkTrue kv)
                    (Prim UnspecifiedOutput TyUnknown)
                    (mkFalse kv)
    in if arg_ty == ret_ty then Just (tup_e, [arg_id], ng1) else Nothing

-- Return Id for argument, and the Name that we're replacing in path conds
mkLamArg :: State t -> NameGen -> LitTable -> Maybe (Id, Name, NameGen)
mkLamArg s ng lt = do
    let eenv = expr_env s
    let tvnv = tyvar_env s

    let (Id lt_arg_name _) = lt_arg lt
    lt_arg_e <- E.deepLookup lt_arg_name eenv
    (unboxed_sym, unboxed_name) <-
        case lt_arg_e of
            App _ (v@(Var i)) -> Just (v, idName i)
            _ -> Nothing

    let lit_ty = typeOf tvnv unboxed_sym
    let (elem_var, ng1) = freshId lit_ty ng
    return (elem_var, unboxed_name, ng1)

-- Make a fully applied primitive tuple with four elements
mkTup4 :: KnownValues -> TypeEnv -> TyVarEnv -> Expr -> Expr -> Expr -> Expr -> Expr
mkTup4 kv tenv tv_env x y z q = t3
    where
        t3 = mkTup kv tenv tv_env x t2
        t2 = mkTup kv tenv tv_env y t1
        t1 = mkTup kv tenv tv_env z q

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

-- (Model function, Success, Partial table function to use with `assume`, Is partial)
mkUnsuccessfulRet :: KnownValues -> TypeEnv -> TyVarEnv -> Expr
mkUnsuccessfulRet kv tenv tv_env =
    mkTup4 kv tenv tv_env
        (Prim UnspecifiedOutput TyUnknown)
        (mkFalse kv)
        (Prim UnspecifiedOutput TyUnknown)
        (mkFalse kv)

-- Convert the literal table to a lambda function, which is then returned
-- For functions returning a boolean, we optimize the representation to be
-- the disjunction of all True path conditions (using `Prim Or`).
-- For other functions, we use `ite`.
litTableToLam :: State t -> NameGen -> LitTable -> (Expr, EESymDiff, NameGen)
litTableToLam s ng lt =
    case litTableToLam' s ng lt of
        Just x -> x
        Nothing -> (mkUnsuccessfulRet kv tenv tv_env, [], ng)
    where
        kv = known_values s
        tenv = type_env s
        tv_env = tyvar_env s

litTableToLam' :: State t -> NameGen -> LitTable -> Maybe (Expr, EESymDiff, NameGen)
litTableToLam' s ng lt =
    if lt_errored lt then
        Just (mkUnsuccessfulRet kv tenv tv_env, [], ng)
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

litTableToLamBool :: State t -> NameGen -> LitTable -> Maybe (Expr, EESymDiff, NameGen)
litTableToLamBool s ng lt = do
    let kv = known_values s
    let tenv = type_env s
    let tv_env = tyvar_env s
    (elem_var, unboxed_name, ng1) <- mkLamArg s ng lt

    let lt_lst = HM.toList $ lt_mapping lt
    let lt_trues = makeAllTrue kv lt_lst

        -- At this point, we know the literal table is non-empty, since we are creating a lambda for
        -- a boolean-returning function
    let or_exp = mkDisjunction kv lt_trues
    let or_exp1 = replaceVar unboxed_name (Var elem_var) or_exp
    let fun_exp = Lam TermL elem_var or_exp1
    let (partial_check, is_partial) =
            createPartialHandler (replaceVar unboxed_name (Var elem_var) lt) kv elem_var
    let tup_exp = mkTup4 kv tenv tv_env
                      fun_exp
                      (mkTrue kv)
                      partial_check
                      is_partial
    return (tup_exp, [elem_var], ng1)

litTableToLamNonBool :: State t -> NameGen -> LitTable -> Maybe (Expr, EESymDiff, NameGen)
litTableToLamNonBool s ng lt = do
    (elem_var, unboxed_name, ng1) <- mkLamArg s ng lt
    let kv = known_values s
    let tv_env = tyvar_env s
    let tenv = type_env s
    let lt_lst = HM.toList $ lt_mapping lt
    -- `Char`s are represented as one character `String`s here, so we
    -- need to extract the first character.
    let wrap e t = if t == tyChar kv
                       then mkApp [Prim SeqNth TyUnknown, e, Lit $ LitInt 0]
                       else e
    -- At this point, we assume there are no `Error`s in the literal table. This
    -- means we have a total function, and we can pick one option to be the default.
    ite_exp <- case lt_lst of
                    ((_ {- We ignore the PathConds for the default -}, def_e):rest) ->
                        Just $ L.foldl'
                                (\prev_exp (pcs, e) ->
                                    mkApp [ Prim Ite TyUnknown
                                          , (pcsToExprBool kv $ PC.toList pcs)
                                          , (wrap e $ typeOf tv_env e)
                                          , prev_exp ]
                                )
                                (wrap def_e $ typeOf tv_env def_e)
                                (reverse rest)
                    _ -> Nothing
    let ite_exp1 = replaceVar unboxed_name (Var elem_var) ite_exp
    let fun_exp = Lam TermL elem_var ite_exp1
    let (partial_check, is_partial) =
            createPartialHandler (replaceVar unboxed_name (Var elem_var) lt) kv elem_var
    let tup_exp = mkTup4 kv tenv tv_env
                      fun_exp
                      (mkTrue kv)
                      partial_check
                      is_partial
    return (tup_exp, [elem_var], ng1)

mkDisjunction :: KnownValues -> [[PathCond]] -> Expr
mkDisjunction kv conds =
    case conds of
        [] -> mkFalse kv
        (hd:tl) ->
            L.foldl'
                (\prev_exp pcs -> mkApp [Prim Or (tripleBoolTy kv), prev_exp, pcsToExprBool kv pcs])
                (pcsToExprBool kv hd)
                tl

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

tripleBoolTy :: KnownValues -> Type
tripleBoolTy kv = mkTyFun [tyBool kv, tyBool kv, tyBool kv]

doubleBoolTy :: KnownValues -> Type
doubleBoolTy kv = mkTyFun [tyBool kv, tyBool kv]

-- Add an expression to the set of seen recursive functions, if we are
-- in literal table mode and the expression is recursive and has a
-- function type
addFunExprLT :: State t -> Expr -> State t
addFunExprLT s expr_ =
    let lts = lit_table_stack s
        eenv = expr_env s
        tvnv = tyvar_env s

        addE lt@(LitTable { lt_rec_funs = ltf }) = lt { lt_rec_funs = HS.insert expr_ ltf }
        s1 = s { lit_table_stack = S.modifyTop addE lts }

        cg = CG.getCallGraph eenv
        isRec e@(Var (Id n _)) = (not $ CG.isFuncNonRecursive cg n) && isTyFun (typeOf tvnv e)
        isRec _ = False

        add_cond = inLitTableMode s && isRec expr_
    in if add_cond then s1 else s

-- Check if an expression is a recursive function that has already
-- been discovered
checkFunExprLT :: State t -> Expr -> Bool
checkFunExprLT s expr_ =
    let lts = lit_table_stack s
    in case S.pop lts of
        Just (lt, _) -> expr_ `HS.member` (lt_rec_funs lt)
        Nothing -> False

-- Pop stack frames until either a `StartedBuilding` literal table
-- frame or the stack is empty
popUntilStartedBuilding :: S.Stack Frame -> S.Stack Frame
popUntilStartedBuilding stck =
    case S.pop stck of
        Just (LitTableFrame (StartedBuilding _) _, _) -> stck
        Just (_, stck1) -> popUntilStartedBuilding stck1
        Nothing -> stck

topLTNonEmpty :: State t -> Bool
topLTNonEmpty s =
    let lts = lit_table_stack s
    in case S.pop lts of
        Just (lt, _) -> ltNonEmpty lt
        Nothing -> False

ltNonEmpty :: LitTable -> Bool
ltNonEmpty lt = not $ null (HM.toList $ lt_mapping lt)

-- If the literal table is partial, we want to create a function that
-- returns True when an input is covered and False when it is not
createPartialHandler :: LitTable -> KnownValues -> Id -> (Expr, Expr)
createPartialHandler lt kv elem_id =
    if not $ lt_partial lt then (Prim UnspecifiedOutput TyUnknown, mkFalse kv)
    else (lam_exp, mkTrue kv)
    where
        lt_conds = map (PC.toList . fst) $ (HM.toList . lt_mapping) lt
        or_exp = mkDisjunction kv lt_conds
        lam_exp = Lam TermL elem_id or_exp

-- Add the current expr into the list of evaluated recursive functions,
-- if applicable. Then, check if we already know the current expr is a
-- recursive function from the current literal table construction process,
-- and if so, split state such that the new state is ready to return a
-- partial table to the caller of buildLitTable#.
-- When not in literal table mode or the current expression is Nothing,
-- none of these events will occur.
splitStateLT :: State t -> Maybe Expr -> (State t, Maybe (State t))
splitStateLT init_s e = res
    where
        res = case e of
                Just e1 -> (addFunExprLT init_s e1, mkLTExtra e1)
                Nothing -> (init_s, Nothing)

        -- We disregard any changes that can be made from evaluation
        -- and pop all the way down to the started building frame
        mkLTExtra e1 =
            if checkFunExprLT init_s e1 && topLTNonEmpty init_s
                then Just $ init_s { exec_stack = popUntilStartedBuilding stck
                                   , lit_table_stack = S.modifyTop mkPartial lts }
                else Nothing

        mkPartial lt = lt { lt_partial = True }

        lts = lit_table_stack init_s
        stck = exec_stack init_s
