-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Execution.Interface
    ( runExecution
    , stdReduce
    ) where

import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language.Support

{-# INLINE runExecution #-}
runExecution :: (Eq t, Reducer r rv t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> Bool -> State t -> Bindings -> IO ([State t], Bindings)
runExecution red hal ord mergeStates s b =
    if mergeStates
        then runReducerMerge red hal s b
        else runReducer red hal ord s b
