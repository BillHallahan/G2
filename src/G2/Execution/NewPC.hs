module G2.Execution.NewPC ( NewPC (..)
                          , newPCEmpty
                          , reduceNewPC ) where

import G2.Language
import qualified G2.Language.PathConds as PC
import qualified G2.Language.ExprEnv as E
import G2.Solver

import Data.List
import Data.Maybe
import G2.Data.Utils
import Data.Traversable

type EEDiff = [(Name, Expr)] -- concrete values to insert in ExprEnv
type EESymDiff = [Id] -- symbolic variables to insert in ExprEnv

data NewPC t = SingleState (State t)
             | SplitStatePieces (State t) [StateDiff]
                
data StateDiff = SD { new_conc_entries :: EEDiff -- ^ New concrete entries for the expr_env
                    , new_sym_entries :: EESymDiff -- ^ New symbolic entries for the expr_env
                    , new_path_conds :: [PathCond] -- ^ New path constraints
                    , concretized :: [Id]
                    , new_true_assert :: Bool
                    }

newPCEmpty :: State t -> NewPC t
newPCEmpty s = SingleState s

-- This will now return a list of States: one for each StateDiff applied to the starting state. The
-- end goal here is to be able to check whether the diffs are able to be used with a Literal Table
reduceNewPC :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NameGen -> NewPC t -> IO (NameGen, [State t])
reduceNewPC _ _ ng (SingleState state) = return (ng, [state])
reduceNewPC solver simplifier ng (SplitStatePieces state state_diffs) =
    mapAccumMaybeM (\ng' sd -> reduceNewPC' solver simplifier ng' state sd) ng state_diffs

-- Make a new State from a StateDiff and a starting State, if the State is reachable
reduceNewPC' :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NameGen -> State t -> StateDiff -> IO (Maybe (NameGen, State t))
reduceNewPC' solver simplifier ng 
             init_state@(State { expr_env = init_eenv, path_conds = state_pc }) 
             (SD {new_conc_entries = nce, new_sym_entries = nse, new_path_conds = pc, concretized = concIds, new_true_assert = nta}) 
    | not (null pc) || not (null concIds) = do
        let ((ng', eenv'), pc') =
                mapAccumR (\(ng_, eenv_) pc_ ->
                                let (ng_', eenv_', pc_') = simplifyPCWithExprEnv simplifier s ng_ eenv_ pc_ in
                                ((ng_', eenv_'), pc_')) (ng, eenv) pc

        let pc'' = map (simplifyPC simplifier s) pc'
            pc''' = concat pc''

        let new_pc = foldr PC.insert state_pc $ pc'''
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
                [] -> PC.fromList pc'''
                _ -> PC.scc' (Nothing:map Just ns) new_pc'

        res <- check solver s rel_pc

        if res == SAT () then
            return $ Just (ng', s')
        else
            return Nothing
    | otherwise = return $ Just (ng, s)
    where
        eenv = E.insertExprs nce $ foldl' (flip E.insertSymbolic) init_eenv nse
        s = init_state { expr_env = eenv, true_assert = nta }

mapAccumMaybeM :: Monad m => (s -> a -> m (Maybe (s, b))) -> s -> [a] -> m (s, [b])
mapAccumMaybeM f s xs = do
    (s', xs') <- mapAccumM f' s xs
    return (s', catMaybes xs')
    where
        f' st x = do
            r <- f st x
            case r of
                Just (s', x') -> return (s', Just x')
                Nothing -> return (st, Nothing)
