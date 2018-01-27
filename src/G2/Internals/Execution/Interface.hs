-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNBreadth
    , runNBreadthNoConstraintChecks
    , runNDepth
    , runNDepthNoConstraintChecks
    ) where

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support
import G2.Internals.Solver.Language

runNBreadth :: SMTConverter ast out io -> io -> [([Rule], State)] -> Int -> IO [([Rule], State)]
runNBreadth _ _ [] _ = return []
runNBreadth _ _ rss 0 = return rss
runNBreadth con hpp rss n = do
    rss' <- return . concat =<< mapM go rss
    runNBreadth con hpp rss' (n - 1)

    where
        go :: ([Rule], State) -> IO [([Rule], State)]
        go (rules, state) = do
            (rule, states) <- reduce con hpp state rules
            return $ map (\s -> (rules ++ [rule], s)) states
 
runNBreadthNoConstraintChecks :: [([Rule], State)] -> Int -> [([Rule], State)]
runNBreadthNoConstraintChecks [] _ = []
runNBreadthNoConstraintChecks rss 0 = rss
runNBreadthNoConstraintChecks rss n = runNBreadthNoConstraintChecks (concatMap go rss) (n - 1)
  where
    go :: ([Rule], State) -> [([Rule], State)]
    go (rules, state) = let (rule, states) = reduceNoConstraintChecks state
                        in map (\s -> (rules ++ [rule], s)) states

runNDepth :: SMTConverter ast out io -> io -> [State] -> Int -> IO [([Rule], State)]
runNDepth con hpp states d = runNDepth' $ map (\s -> (([], s), d)) states
  where
    runNDepth' :: [(([Rule], State), Int)] -> IO [([Rule], State)]
    runNDepth' [] = return []
    runNDepth' ((rss, 0):xs) = return . (:) rss =<< runNDepth' xs
    runNDepth' ((((rs, s), n)):xs) = do
        (app_rule, reduceds) <- reduce con hpp s rs
        
        let mod_info = map (\s' -> ((rs ++ [app_rule], s'), n - 1)) reduceds
        
        runNDepth' (mod_info ++ xs)

runNDepthNoConstraintChecks :: [State] -> Int -> [([Rule], State)]
runNDepthNoConstraintChecks states d = runNDepthNCC' $ map (\s -> (([], s), d)) states
  where
    runNDepthNCC' :: [(([Rule], State), Int)] -> [([Rule], State)]
    runNDepthNCC' [] = []
    runNDepthNCC' ((rss, 0):xs) = rss : runNDepthNCC' xs
    runNDepthNCC' ((((rs, s), n)):xs) =
        let (app_rule, reduceds) = reduceNoConstraintChecks s
            mod_info = map (\s' -> ((rs ++ [app_rule], s'), n - 1)) reduceds
        in runNDepthNCC' (mod_info ++ xs)
