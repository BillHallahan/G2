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
-- translates to re.comp, `=` translates to just the character string (from str.to_re)
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
            (Prim InRe TyUnknown)
            str_e)
        (App
            (Prim ReStar TyUnknown)
            (createAllRegex kv tenv lt_trues))

createAllRegex :: KnownValues -> TypeEnv -> [[PathCond]] -> Expr
createAllRegex _ _ [] = Prim ReNone TyUnknown
createAllRegex kv tenv (pc_list:pc_lists) =
    App (App (Prim ReUnion TyUnknown) (pcListToRegex kv tenv pc_list)) (createAllRegex kv tenv pc_lists)

-- We need the intersection of all of these path conditions
pcListToRegex :: KnownValues -> TypeEnv -> [PathCond] -> Expr
pcListToRegex _ _ [] = Prim ReAll TyUnknown
pcListToRegex kv tenv (pc:pcs) =
    case pc of
        ExtCond exp bool -> undefined
        -- The expression here never matters, since we are always either matching or
        -- not matching the char to a variable (which should always be the same and
        -- does not matter for our regex conversion)
        AltCond (LitChar c) _ bool -> 
            if bool
                then App 
                        (App 
                            (Prim ReInter TyUnknown)
                            (App 
                                (Prim ToRe TyUnknown) 
                                (toSingletonStringExpr kv tenv c)))
                        (pcListToRegex kv tenv pcs)
                else App 
                        (App 
                            (Prim ReInter TyUnknown)
                            (App 
                                (Prim ReComp TyUnknown) 
                                (App 
                                    (Prim ToRe TyUnknown) 
                                    (toSingletonStringExpr kv tenv c))))
                        (pcListToRegex kv tenv pcs)
        _ -> error $ "unhandled pc in pcListToRegex:\n" ++ show pc

toSingletonStringExpr :: KnownValues -> TypeEnv -> Char -> Expr
toSingletonStringExpr kv tenv c =
    let cons = mkCons kv tenv
        charTy = Type (tyChar kv)
        charExpr = App (mkDCChar kv tenv) (Lit (LitChar c))
        emptyList = App (mkEmpty kv tenv) charTy
    in mkApp [cons, charTy, charExpr, emptyList]