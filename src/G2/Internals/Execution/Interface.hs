-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runExecution
    , runNDepthNoConstraintChecks
    , stdReduce
    ) where

import G2.Internals.Config.Config

import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Language.Support
import G2.Internals.Solver.Language

{-# INLINE runExecution #-}
runExecution :: (Reducer r t, Halter h hv t, Orderer or orv sov t) => r -> h -> or -> SMTConverter ast out io -> io -> orv -> [State t] -> Config -> IO [([Int], State t)]
runExecution = runReducer

runNDepthNoConstraintChecks :: [State t] -> Int -> [State t]
runNDepthNoConstraintChecks states d = runNDepthNCC' $ map (\s -> (s, d)) states
  where
    runNDepthNCC' :: [(State t, Int)] -> [State t]
    runNDepthNCC' [] = []
    runNDepthNCC' ((rss, 0):xs) = rss : runNDepthNCC' xs
    runNDepthNCC' ((s, n):xs) =
        let reduceds = reduceNoConstraintChecks stdReduce undefined s
            mod_info = map (\s' -> (s', n - 1)) reduceds
        in runNDepthNCC' (mod_info ++ xs)
