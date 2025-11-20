{-# LANGUAGE PatternSynonyms #-}

module G2.Execution.ExecSkip 
    (
        ExecOrSkip (Skip),
        pattern Exec,
        NRPCMemoTable,
        isExecOrSkip,
        checkDelayability,

        ReachesSymMemoTable,
        reachesSymbolicMemo
    ) where

import G2.Execution.Internals.ExecSkip