-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Execution.Interface
    ( runExecutionToProcessed
    , runExecution
    , stdReduce
    ) where

import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language.Support
import G2.Solver

{-# INLINE runExecutionToProcessed #-}
runExecutionToProcessed :: (Reducer r rv t, Halter h hv t, Orderer or sov b t, Solver solver) => r -> h -> or -> solver -> State t -> Bindings -> IO (Processed (State t), Bindings)
runExecutionToProcessed = runReducer

{-# INLINE runExecution #-}
runExecution :: (Reducer r rv t, Halter h hv t, Orderer or sov b t, Solver solver) => r -> h -> or -> solver -> State t -> Bindings -> IO ([State t], Bindings)
runExecution r h ord solver s b = do
    (pr, b') <- runReducer r h ord solver s b
    return (accepted pr, b')
