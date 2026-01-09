module G2.Execution.NewPC ( NewPC (..)
                          , newPCEmpty
                          , newPCNoStates
                          , reduceNewPC ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import qualified G2.Language.TyVarEnv as TV
import G2.Solver

import Data.List
import Data.Maybe
import G2.Data.Utils
import Data.Traversable
import G2.Execution.MutVar

data NewPC t = SingleState (State t)
             | SplitStatePieces (State t) [StateDiff]

newPCEmpty :: State t -> NewPC t
newPCEmpty s = SingleState s

-- A NewPC that corresponds to no states to look for, as opposed to newPCEmpty which returns one state
newPCNoStates :: State t -> NewPC t
newPCNoStates s = SplitStatePieces s []

-- This will now return a list of States: one for each StateDiff applied to the starting state. The
-- end goal here is to be able to check whether the diffs are able to be used with a literal table
reduceNewPC :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NameGen -> NewPC t -> IO (NameGen, [State t])
reduceNewPC _ _ ng (SingleState state) = return (ng, [state])
reduceNewPC solver simplifier ng (SplitStatePieces state state_diffs) =
    mapAccumMaybeM (\ng' sd -> reduceNewPC' solver simplifier ng' state sd) ng state_diffs

-- Make a new State from a StateDiff and a starting State, if the State is reachable
reduceNewPC' :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> NameGen -> State t -> StateDiff -> IO (Maybe (NameGen, State t))
reduceNewPC' solver simplifier ng
             init_state@(State { expr_env = init_eenv, tyvar_env = init_tvenv
                               , path_conds = state_pc })
             (SD { new_conc_entries = nce
                 , new_sym_entries = nse
                 , new_path_conds = pc
                 , concretized = concIds
                 , new_true_assert = nta
                 , new_assert_ids = nai
                 , new_curr_expr = n_curre
                 , new_conc_types = nct
                 , new_sym_types = nst
                 , new_mut_vars = nmv })
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
        insertInOrder inserter exprs_ eenv_ = foldl' (flip $ uncurry inserter) eenv_ exprs_
        insertSymInOrder inserter syms_ eenv_ = foldl' (flip inserter) eenv_ syms_

        eenv = insertInOrder E.insert nce $ insertSymInOrder E.insertSymbolic nse init_eenv
        tvenv = insertInOrder TV.insert nct $ insertSymInOrder TV.insertSymbolic nst init_tvenv
        state = newMutVars init_state nmv
        s = state {
            expr_env = eenv, tyvar_env = tvenv,
            true_assert = nta, assert_ids = nai,
            curr_expr = n_curre }

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
