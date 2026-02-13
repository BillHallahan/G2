module G2.Execution.LiteralTable 
    ( introduceLitTable
    , inLitTableMode
    , updateLiteralTable
    , getLTArg
    , stopUpdateLastExpl
    ) where

import qualified G2.Language.Stack as S
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