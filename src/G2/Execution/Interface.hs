-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Execution.Interface
    ( runExecutionToProcessed
    , runExecution
    , stdReduce
    ) where

import G2.Config.Config
import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language.Support
import G2.Language.Naming
import G2.Solver.Simplifier

{-# INLINE runExecutionToProcessed #-}
runExecutionToProcessed :: (Reducer r rv t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> State t -> Bindings -> IO (Processed (State t), Bindings)
runExecutionToProcessed = runReducer

{-# INLINE runExecution #-}
runExecution :: (Eq t, Named t, Reducer r rv t, Halter h hv t, Orderer or sov b t, Simplifier simplifier)
                => r -> h -> or -> simplifier -> Merging -> State t -> Bindings -> IO ([State t], Bindings)
runExecution red hal ord simplifier mergeStates s b =
    case mergeStates of
        Merging -> runReducerMerge red hal simplifier s b
        NoMerging -> do (pr, b') <- runReducer red hal ord s b
                        return (accepted pr, b')
