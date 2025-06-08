module G2.Execution.NewPC.Handling ( reduceNewPC ) where

import G2.Language
import qualified G2.Language.PathConds as PC
import G2.Solver
import G2.Execution.NewPC.Type

reduceNewPC :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NewPC t -> IO (Maybe (State t))
reduceNewPC solver simplifier
            (NewPC { state = s@(State { expr_env = eenv, path_conds = spc })
                   , new_pcs = pc
                   , concretized = concIds })
    | not (null pc) || not (null concIds) = do
        let eenv' = foldr (updateExprEnvPC simplifier s) eenv pc

        let pc' = map (simplifyPC simplifier s) pc
            pc'' = concat pc'

        let new_pc = foldr PC.insert spc $ pc''
            new_pc' = foldr (simplifyPCs simplifier s) new_pc pc

            s' = s { expr_env = eenv', path_conds = new_pc' }

        -- Optimization
        -- We replace the path_conds with only those that are directly affected by the new path constraints.
        -- This allows for more efficient solving, and in some cases may change an Unknown into a SAT or UNSAT.
        --
        -- Note that the simplifier might eliminate variables from new path constraints (by substituting them with constants,
        -- for example), but we still need to make sure that such substititions don't violate exisitng path constraints.
        -- For this reason, we extract names for the original (unsimplified) path constraints
        let ns = (concatMap PC.varNamesInPC pc) ++ namesList concIds
            rel_pc = case ns of
                [] -> PC.fromList pc''
                _ -> PC.scc ns new_pc'

        res <- check solver s rel_pc

        if res == SAT () then
            return $ Just s'
        else
            return Nothing
    | otherwise = return $ Just s
