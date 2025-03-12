-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Execution.Interface
    ( runExecutionToProcessed
    , runExecution
    , stdReduce
    ) where

import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Interface.ExecRes
import G2.Language.Support

{-# INLINE runExecutionToProcessed #-}
runExecutionToProcessed :: (Monad m, Ord b) => Reducer m rv t -> Halter m hv r t -> Orderer m sov b r t -> (State t -> Bindings -> m (Maybe r)) -> State t -> Bindings -> m (Processed r (State t), Bindings)
runExecutionToProcessed = runReducer

{-# INLINE runExecution #-}
runExecution :: (Monad m, Ord b) => Reducer m rv t -> Halter m hv r t -> Orderer m sov b r t -> (State t -> Bindings -> m (Maybe r)) -> State t -> Bindings -> m ([r], Bindings)
runExecution r h ord solve_r s b = do
    (pr, b') <- runReducer r h ord solve_r s b
    return (accepted pr, b')
