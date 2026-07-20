module G2.Execution.NewPC ( NewPC (..)
                          , newPCEmpty
                          , newDefNames
                          , newPCNoStates
                          , reduceNewPC
                          , addPCsToState
                          , reduceStateDiff
                          , reduceToFirstDiff ) where

import G2.Data.Utils
import qualified G2.Execution.DataConPCMap as DCPC
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import qualified G2.Language.TyVarEnv as TV
import G2.Solver.Simplifier
import G2.Solver.Solver

import G2.Execution.MutVar
import G2.Execution.LiteralTable
import G2.Config.Config (DiscardUnknownStates (KeepUnknown))

import Data.List
import Data.Maybe
import qualified Data.Sequence as Seq

data NewPC t = NoState
             | SingleState (State t)
             | SplitStatePieces (State t) [StateDiff]


newPCEmpty :: State t -> NewPC t
newPCEmpty s = SingleState s

newDefNames :: NewPC t -> Seq.Seq Name
newDefNames NoState = Seq.empty
newDefNames (SingleState _) = Seq.empty
newDefNames (SplitStatePieces _ sds) =
    mconcat $ map (\sd ->
                  (Seq.fromList . map fst $ new_conc_entries sd)
                <> Seq.fromList (concatMap PC.varNamesInPC (new_path_conds sd))) sds

-- A NewPC that corresponds to no states to look for, as opposed to newPCEmpty which returns one state
newPCNoStates :: State t -> NewPC t
newPCNoStates s = SplitStatePieces s []

-- This will now return a list of States: one for each StateDiff applied to the starting state. The
-- end goal here is to be able to check whether the diffs are able to be used with a literal table
-- When in literal table building mode (lit table stack is non-empty), this will take the first reachable
-- diff and put it onto the stack as an Exploring (leaving the rest of the states as Diffs on the stack)
reduceNewPC :: (Solver solver, Simplifier simplifier)
            => DiscardUnknownStates
            -> solver
            -> simplifier
            -> NameGen
            -> NewPC t
            -> IO (NameGen, [State t])
reduceNewPC _ _ _  ng NoState = return (ng, [])
reduceNewPC _ _ _ ng (SingleState state) = return (ng, [state])
reduceNewPC discard_unknown_states solver simplifier ng (SplitStatePieces state state_diffs)
    | inLitTableMode state
    , scrut_smt_rep || all (null . new_conc_entries) state_diffs = do
        let state_diffs' = map elim_conc_entries state_diffs
        res <- reduceToFirstDiff discard_unknown_states solver simplifier ng state state_diffs'
        case res of
            Just (ng', first_s, pcs, other_diffs) ->
                let prev_stck = stopUpdateLastExpl $ exec_stack first_s
                    diffs_pushed = foldr S.push prev_stck $ map wrap other_diffs
                    expl_pushed = S.push (LitTableFrame (Exploring (PC.fromList pcs)) True) diffs_pushed

                    glob_pc' = foldr PC.insert (global_lit_table_pc state) force_specific_cons_args
                in return (ng', [first_s { exec_stack = expl_pushed, global_lit_table_pc = glob_pc' }])
            Nothing -> return (ng, [])
    | otherwise =
        mapAccumMaybeM (\ng' sd -> reduceStateDiff discard_unknown_states solver simplifier ng' state sd) ng state_diffs
    where
        kv = known_values state
        tenv = type_env state
        tv_env = tyvar_env state
        ce = curr_expr state
        unwrapped_ce = getCurrExpr ce

        scrut_smt_rep = case unwrapped_ce of
                            Case e _ _ _ 
                                | DCPC.allInDCPC tenv $ typeOf tv_env e -> True
                                | TyCon n _ <- typeOf tv_env e -> n == KV.tyBool kv
                            _ -> False

        getCurrExpr (CurrExpr _ e) = e

        -- For types being branched on in literal tables, we want to avoid concretization,
        -- only using the path conds
        elim_conc_entries d = d { new_conc_entries = []}

        force_specific_cons_args = map (uncurry consImpliesEq) (concatMap new_conc_entries state_diffs)
        consImpliesEq n e
            | Data dc <- appCenter e =
                let
                    v = Var (Id n $ typeOf tv_env e)
                    has_cons = App (Prim (IsConstructor dc) TyUnknown) v
                    eq_dc = mkApp [ Prim Eq TyUnknown, v, e]
                in
                ExtCond ( mkApp [Prim Implies TyUnknown, has_cons, eq_dc]) True 
            | otherwise = error "Expected constructor"

        wrap diff = LitTableFrame (Diff diff (path_conds state)) True

-- Find the first diff to explore, when in literal table building mode
reduceToFirstDiff :: (Solver solver, Simplifier simplifier)
                  => DiscardUnknownStates
                  -> solver
                  -> simplifier
                  -> NameGen
                  -> State t
                  -> [StateDiff]
                  -> IO (Maybe (NameGen, State t, [PathCond], [StateDiff]))
reduceToFirstDiff _ _ _ _ _ [] = return Nothing
reduceToFirstDiff dus solver simplifier ng state (diff:diffs) = do
    res <- reduceStateDiff dus solver simplifier ng state diff
    case res of
        Just (ng', s') -> return $ Just (ng', s', new_path_conds diff, diffs)
        Nothing -> reduceToFirstDiff dus solver simplifier ng state diffs

-- Make a new State from a StateDiff and a starting State, if the State is reachable
reduceStateDiff :: (Solver solver, Simplifier simplifier)
                => DiscardUnknownStates
                -> solver
                -> simplifier
                -> NameGen
                -> State t
                -> StateDiff
                -> IO (Maybe (NameGen, State t))
reduceStateDiff discard_unknown_states solver simplifier ng
             init_state@(State { expr_env = init_eenv, tyvar_env = init_tvenv })
             (SD { new_conc_entries = nce
                 , new_sym_entries = nse
                 , new_path_conds = pc
                 , concretized = conc_ids
                 , new_true_assert = nta
                 , new_assert_ids = nai
                 , new_curr_expr = n_curre
                 , new_conc_types = nct
                 , new_sym_types = nst
                 , new_mut_vars = nmv }) = addPCsToState discard_unknown_states solver simplifier ng s conc_ids pc
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

addPCsToState :: (Solver solver, Simplifier simplifier)
                => DiscardUnknownStates
                -> solver
                -> simplifier
                -> NameGen
                -> State t
                -> [Id]
                -> [PathCond]
                -> IO (Maybe (NameGen, State t))
addPCsToState discard_unknown_states solver simplifier ng
             s@(State { expr_env = eenv
                      , path_conds = state_pc })
             conc_ids pc
    | not (null pc) || not (null conc_ids) = do
        let ((ng', eenv'), pc') =
                mapAccumR (\(ng_, eenv_) pc_ ->
                                let (ng_', eenv_', pc_') = simplifyPCWithExprEnv simplifier s ng_ eenv_ pc_ in
                                ((ng_', eenv_'), pc_')) (ng, eenv) pc

        let pc'' = concat pc'

        let new_pc = foldr PC.insert state_pc pc''
            new_pc' = foldr (simplifyPCs simplifier s) new_pc pc

            s' = s { expr_env = eenv', path_conds = new_pc' }

        -- Optimization
        -- We replace the path_conds with only those that are directly affected by the new path constraints.
        -- This allows for more efficient solving, and in some cases may change an Unknown into a SAT or UNSAT.
        --
        -- Note that the simplifier might eliminate variables from new path constraints (by substituting them with constants,
        -- for example), but we still need to make sure that such substititions don't violate exisitng path constraints.
        -- For this reason, we extract names for the original (unsimplified) path constraints
        let ns = (concatMap PC.varNamesInPC pc) ++ namesList conc_ids
            rel_pc = case ns of
                [] -> PC.fromList pc''
                _ -> PC.scc' (Nothing:map Just ns) new_pc'

        res <- check solver s rel_pc

        case res of
            SAT () -> return $ Just (ng', s')
            UNSAT () -> return Nothing
            Unknown _ _ | discard_unknown_states == KeepUnknown -> return $ Just (ng', s')
                        | otherwise -> return Nothing
    | otherwise = return $ Just (ng, s)

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

