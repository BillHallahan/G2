{-# LANGUAGE PatternSynonyms #-}

module G2.Execution.ExecSkip 
    (
        ExecOrSkip (Skip),
        pattern Exec,
        NRPCMemoTable,
        isExecOrSkip,
        checkDelayability,

        ReachesSymMemoTable,
        reachesSymbolic
    ) where

import G2.Execution.Internals.ExecSkip