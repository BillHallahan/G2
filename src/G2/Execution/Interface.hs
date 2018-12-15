-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Execution.Interface
    ( runExecution
    , runNDepthNoConstraintChecks
    , stdReduce
    ) where

import G2.Config.Config

import G2.Execution.Reducer
import G2.Execution.Rules
import G2.Language.Support

{-# INLINE runExecution #-}
runExecution :: (Reducer r t, Halter h hv t, Orderer or sov b t) => r -> h -> or -> Config -> State t -> IO [([Int], State t)]
runExecution = runReducer

runNDepthNoConstraintChecks :: Config -> [State t] -> Int -> [State t]
runNDepthNoConstraintChecks config states d = runNDepthNCC' $ map (\s -> (s, d)) states
  where
    runNDepthNCC' :: [(State t, Int)] -> [State t]
    runNDepthNCC' [] = []
    runNDepthNCC' ((rss, 0):xs) = rss : runNDepthNCC' xs
    runNDepthNCC' ((s, n):xs) =
        let reduceds = reduceNoConstraintChecks stdReduce s
            mod_info = map (\s' -> (s', n - 1)) reduceds
        in runNDepthNCC' (mod_info ++ xs)
