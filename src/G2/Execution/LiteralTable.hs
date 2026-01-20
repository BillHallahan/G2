module G2.Execution.LiteralTable 
    ( introduceLitTable
    ) where

import qualified G2.Language.Stack as S
import G2.Language
import qualified Data.HashMap.Lazy as HM

introduceLitTable :: State t -> Name -> State t
introduceLitTable s n = s { lit_table_stack = lts
                          , exec_stack = es }
    where lts = S.push (HM.empty) (lit_table_stack s)
          es = S.push (LitTableFrame $ StartedBuilding n) (exec_stack s)