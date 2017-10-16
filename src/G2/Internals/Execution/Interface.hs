-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNBreadth
    , runNDepth
    ) where

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support

runNBreadth :: [([Rule], State)] -> Int -> [([Rule], State)]
runNBreadth [] _ = []
runNBreadth rss 0 = rss
runNBreadth rss n = runNBreadth (concatMap go rss) (n - 1)
  where
    go :: ([Rule], State) -> [([Rule], State)]
    go (rules, state) = let (rule, states) = reduce state
                        in map (\s -> (rules ++ [rule], s)) states

runNDepth :: [State] -> Int -> [([Rule], State)]
runNDepth states d = runNDepth' $ map (\s -> (([], s), d)) states
  where
    runNDepth' :: [(([Rule], State), Int)] -> [([Rule], State)]
    runNDepth' [] = []
    runNDepth' ((rss, 0):xs) = rss : runNDepth' xs
    runNDepth' ((((rs, s), n)):xs) =
        let (app_rule, reduceds) = reduce s
            mod_info = map (\s' -> ((rs ++ [app_rule], s'), n - 1)) reduceds
        in runNDepth' (mod_info ++ xs)