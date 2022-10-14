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

import Control.Monad.IO.Class 

{-# INLINE runExecutionToProcessed #-}
runExecutionToProcessed :: (MonadIO m, Halter h hv t, Orderer or sov b t) => Reducer m rv t -> h -> or -> State t -> Bindings -> m (Processed (State t), Bindings)
runExecutionToProcessed = runReducer

{-# INLINE runExecution #-}
runExecution :: (MonadIO m, Halter h hv t, Orderer or sov b t) => Reducer m rv t -> h -> or -> State t -> Bindings -> m ([State t], Bindings)
runExecution r h ord s b = do
    (pr, b') <- runReducer r h ord s b
    return (accepted pr, b')
