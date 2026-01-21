module G2.Execution.LiteralTable 
    ( introduceLitTable
    , inLitTableMode
    ) where

import qualified G2.Language.Stack as S
import G2.Language.Syntax
import G2.Language.Support
import qualified Data.HashMap.Lazy as HM
import Data.Maybe

introduceLitTable :: State t -> Name -> State t
introduceLitTable s n = s { lit_table_stack = lts
                          , exec_stack = es }
    where lts = S.push (HM.empty) (lit_table_stack s)
          es = S.push (LitTableFrame $ StartedBuilding n) (exec_stack s)

inLitTableMode :: State t -> Bool
inLitTableMode s = let lit_stack = lit_table_stack s
                       non_empty = isJust $ S.pop lit_stack
                   in non_empty