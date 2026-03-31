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
import G2.Language.Typing
import G2.Language.Syntax
import G2.Language.Support
import G2.Language.Expr
import qualified Data.HashMap.Lazy as HM
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

-- We only want the `True` path conds from the lit table, which we then
-- convert into a large regex, with each path condition as an alternative,
-- through re.union. `&&` translates to re.inter, `||` translates to re.union, 
-- `<` and `>` translate to range (with the max / min character in unicode), `not`
-- translates to re.comp, `=` translates to just the character string (from str.to_re).
-- This will match (or not match) a full string using `str.in_re` and `re.star`.
litTableToAllRe :: State t -> LitTable -> Expr -> Expr
litTableToAllRe s lt str_e = 
    let kv = known_values s
        tenv = type_env s
        lt_lst = HM.toList $ lt_mapping lt
        lt_bools = makeAllBools kv lt_lst
        lt_trues = map fst $ filter snd lt_bools
    -- For a regex that can match a string, we need the Kleene star of all possible
    -- regex that lead to True in the lit table
    in App 
        (App
            (inRe kv)
            str_e)
        (App
            (reStar kv)
            (createAllRegex kv tenv lt_trues))

createAllRegex :: KnownValues -> TypeEnv -> [[PathCond]] -> Expr
createAllRegex kv _ [] = (reNone kv)
createAllRegex kv tenv (pc_list:pc_lists) =
    App (App (reUnion kv) (pcListToRegexAll kv tenv pc_list)) (createAllRegex kv tenv pc_lists)

-- We need the intersection of all of these path conditions
pcListToRegexAll :: KnownValues -> TypeEnv -> [PathCond] -> Expr
pcListToRegexAll kv _ [] = reAllChar kv
pcListToRegexAll kv tenv (pc:pcs) =
    case pc of
        ExtCond expr bool -> makeExtCondReAll kv tenv bool expr pcs
        -- The expression here never matters, since we are always either matching or
        -- not matching the char to a variable (which should always be the same and
        -- does not matter for our regex conversion)
        AltCond (LitChar c) _ bool -> makeAltCondReAll kv tenv bool c pcs
        _ -> error $ "unhandled pc in pcListToRegexAll:\n" ++ show pc

makeAltCondReAll :: KnownValues -> TypeEnv -> Bool -> Char -> [PathCond] -> Expr
makeAltCondReAll kv tenv b c nxt_pcs = let chr_re = App (toRe kv) (toSingletonStringExpr kv tenv c)
                                           chr_comp_re = if b then chr_re else App (reComp kv) chr_re
                                       in App (App (reInter kv) chr_comp_re) (pcListToRegexAll kv tenv nxt_pcs)

makeExtCondReAll :: KnownValues -> TypeEnv -> Bool -> Expr -> [PathCond] -> Expr
makeExtCondReAll kv tenv bool expr nxt_pcs = mkFullRe bool expr
    -- This should be the subset of path conds that appear in Char -> Bool functions
    where
        mkRe e = case unApp e of
                    [Prim StrGt _, Var (Id _ _), Lit (LitChar c)] ->
                        if c == maxChr 
                            then reNone kv 
                            else mkApp [ reRange kv
                                       , toSingletonStringExpr kv tenv $ succ c
                                       , toSingletonStringExpr kv tenv maxChr]
                    [Prim StrGe _, Var (Id _ _), Lit (LitChar c)] ->
                        mkApp [ reRange kv
                              , toSingletonStringExpr kv tenv c
                              , toSingletonStringExpr kv tenv maxChr]
                    [Prim StrLt _, Var (Id _ _), Lit (LitChar c)] ->
                        if c == minChr
                            then reNone kv
                            else mkApp [ reRange kv
                                       , toSingletonStringExpr kv tenv minChr
                                       , toSingletonStringExpr kv tenv $ pred c]
                    [Prim StrLe _, Var (Id _ _), Lit (LitChar c)] ->
                        mkApp [ reRange kv
                              , toSingletonStringExpr kv tenv minChr
                              , toSingletonStringExpr kv tenv c]
                    [Prim StrGt ty, l@(Lit (LitChar _)), v@(Var (Id _ _))] -> mkRe $ mkApp [Prim StrLe ty, v, l]
                    [Prim StrGe ty, l@(Lit (LitChar _)), v@(Var (Id _ _))] -> mkRe $ mkApp [Prim StrLt ty, v, l]
                    [Prim StrLt ty, l@(Lit (LitChar _)), v@(Var (Id _ _))] -> mkRe $ mkApp [Prim StrGe ty, v, l]
                    [Prim StrLe ty, l@(Lit (LitChar _)), v@(Var (Id _ _))] -> mkRe $ mkApp [Prim StrGt ty, v, l]
                    [Prim And _, e1, e2] -> mkApp [reInter kv, mkRe e1, mkRe e2]
                    [Prim Or _, e1, e2] -> mkApp [reUnion kv, mkRe e1, mkRe e2]
                    [Prim Not _, e1] -> mkApp [reComp kv, mkRe e1]
                    [Prim Gt ty, e1, e2] -> mkRe $ mkApp [Prim StrGt ty, e1, e2]
                    [Prim Ge ty, e1, e2] -> mkRe $ mkApp [Prim StrGe ty, e1, e2]
                    [Prim Lt ty, e1, e2] -> mkRe $ mkApp [Prim StrLt ty, e1, e2]
                    [Prim Le ty, e1, e2] -> mkRe $ mkApp [Prim StrLe ty, e1, e2]
                    [Prim Eq _, Var (Id _ _), Lit (LitChar c)] -> undefined
                    _ -> error $ "unhandled expr in makeExtCondReAll:\n" ++ show e
        mkFullRe b e =
            let re = mkRe e
                re_comp = if b then re else App (reComp kv) re
            in mkApp [reInter kv, re_comp, pcListToRegexAll kv tenv nxt_pcs]

maxChr :: Char
maxChr = maxBound

minChr :: Char
minChr = minBound
                    
toSingletonStringExpr :: KnownValues -> TypeEnv -> Char -> Expr
toSingletonStringExpr kv tenv c =
    let cons = mkCons kv tenv
        charTy = Type (tyChar kv)
        charExpr = App (mkDCChar kv tenv) (Lit (LitChar c))
        emptyList = App (mkEmpty kv tenv) charTy
    in mkApp [cons, charTy, charExpr, emptyList]

inRe :: KnownValues -> Expr
inRe kv = Prim InRe $ mkTyFun [tyString kv, tyString kv, tyBool kv]

toRe :: KnownValues -> Expr
toRe kv = Prim ToRe $ mkTyFun [tyString kv, tyString kv]

reNone :: KnownValues -> Expr
reNone kv = Prim ReNone $ tyString kv

reAll :: KnownValues -> Expr
reAll kv = Prim ReAll $ tyString kv

reAllChar :: KnownValues -> Expr
reAllChar kv = Prim ReAllChar $ tyString kv

reConcat :: KnownValues -> Expr
reConcat kv = Prim ReConcat $ mkTyFun [tyString kv, tyString kv, tyString kv]

reUnion :: KnownValues -> Expr
reUnion kv = Prim ReUnion $ mkTyFun [tyString kv, tyString kv, tyString kv]

reInter :: KnownValues -> Expr
reInter kv = Prim ReInter $ mkTyFun [tyString kv, tyString kv, tyString kv]

reStar :: KnownValues -> Expr
reStar kv = Prim ReStar $ mkTyFun [tyString kv, tyString kv]

reRange :: KnownValues -> Expr
reRange kv = Prim ReRange $ mkTyFun [tyString kv, tyString kv, tyString kv]

reComp :: KnownValues -> Expr
reComp kv = Prim ReComp $ mkTyFun [tyString kv, tyString kv]