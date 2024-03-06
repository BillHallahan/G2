module G2.Execution.NewPC ( NewPC (..)
                          , newPCEmpty
                          , reduceNewPC ) where

import G2.Language
import qualified G2.Language.PathConds as PC
import G2.Solver

import qualified Data.List as L

data NewPC t = NewPC { state :: State t
                     , new_pcs :: [PathCond]
                     , concretized :: [Id] }

newPCEmpty :: State t -> NewPC t
newPCEmpty s = NewPC { state = s, new_pcs = [], concretized = []}

reduceNewPC :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NewPC t -> IO (Maybe (State t))
reduceNewPC solver simplifier
            (NewPC { state = s@(State { path_conds = spc })
                   , new_pcs = pc
                   , concretized = concIds })
    | not (null pc) || not (null concIds) = do
        let (s', pc') = L.mapAccumL (simplifyPC simplifier) s pc
            pc'' = concat pc'


        -- Optimization
        -- We replace the path_conds with only those that are directly
        -- affected by the new path constraints
        -- This allows for more efficient solving, and in some cases may
        -- change an Unknown into a SAT or UNSAT
        let new_pc = foldr PC.insert spc $ pc''
            new_pc' = foldr (simplifyPCs simplifier s') new_pc pc''

            s'' = s' {path_conds = new_pc'}

        let ns = (concatMap PC.varNamesInPC pc) ++ namesList concIds
            rel_pc = case ns of
                [] -> PC.fromList pc''
                _ -> PC.scc ns new_pc'

        res <- check solver s' rel_pc
        print ("Result of sat: " ++ show res)

        if res == SAT () then
            return $ Just s''
        else
            return Nothing
    | otherwise = return $ Just s
