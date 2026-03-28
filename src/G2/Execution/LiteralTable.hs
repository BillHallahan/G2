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
import G2.Language.Syntax
import G2.Language.Support
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
makeAllPrimBools :: [(PathConds, Expr)] -> [([PathCond], Expr)]
makeAllPrimBools [] = []
makeAllPrimBools ((pcs, e):xs) | isBool e = (PC.toList pcs, e):makeAllPrimBools xs
makeAllPrimBools ((pcs, e):xs) = 
    let lst1 = PC.toList pcs
        pc = undefined
        lst2 = pc:lst1
    in error "todo, makeAllPrimBools"

isBool :: Expr -> Bool
isBool (Data (DataCon _ (TyCon (Name "Bool" _ _ _) _) _ _)) = True
isBool _ = False

-- We only want the `True` path conds from the lit table, which we then
-- convert into a large regex, with each path condition as an alternative,
-- through re.union. `&&` translates to re.inter, `||` translates to re.union, 
-- `<` and `>` translate to range (with the max / min character in unicode), `not`
-- translates to re.comp, `=` translates to just the character string (from str.to_re)
litTableToAllRe :: LitTable -> Expr
litTableToAllRe lt = 
    let lt_lst = makeAllPrimBools (HM.toList $ lt_mapping lt)
    in error $ "todo\n" ++ show lt_lst