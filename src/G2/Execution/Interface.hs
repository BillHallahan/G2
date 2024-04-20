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

{-# INLINE runExecutionToProcessed #-}
runExecutionToProcessed :: (Monad m, Ord b) => Reducer m rv t -> Halter m hv t -> Orderer m sov b t -> State t -> Bindings -> m (Processed (State t), Bindings)
runExecutionToProcessed = runReducer

{-# INLINE runExecution #-}
runExecution :: (Monad m, Ord b) => Reducer m rv t -> Halter m hv t -> Orderer m sov b t -> State t -> Bindings -> m ([State t], Bindings)
runExecution r h ord s b = do
    (pr, b') <- runReducer r h ord s b
    return (accepted pr, b')
