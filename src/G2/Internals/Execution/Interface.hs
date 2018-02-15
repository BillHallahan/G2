-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNBreadth
    , runNBreadthNoConstraintChecks
    , runNDepth
    , runNDepthNoConstraintChecks
    , stdReduce
    ) where

import G2.Internals.Config.Config

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support
import G2.Internals.Solver.Language
import G2.Lib.Printers

import Data.List
import System.Directory

runNBreadth :: SMTConverter ast out io -> io -> [([Rule], State t)] -> Int -> IO [([Rule], State t)]
runNBreadth _ _ [] _ = return []
runNBreadth _ _ rss 0 = return rss
runNBreadth con hpp rss n = do
    rss' <- return . concat =<< mapM go rss
    runNBreadth con hpp rss' (n - 1)

    where
        go :: ([Rule], State t) -> IO [([Rule], State t)]
        go (rules, state) = do
            (rule, states) <- reduce stdReduce con hpp undefined state
            return $ map (\s -> (rules ++ [rule], s)) states
 
runNBreadthNoConstraintChecks :: [([Rule], State t)] -> Int -> [([Rule], State t)]
runNBreadthNoConstraintChecks [] _ = []
runNBreadthNoConstraintChecks rss 0 = rss
runNBreadthNoConstraintChecks rss n = runNBreadthNoConstraintChecks (concatMap go rss) (n - 1)
  where
    go :: ([Rule], State t) -> [([Rule], State t)]
    go (rules, state) = let (rule, states) = reduceNoConstraintChecks stdReduce undefined state
                        in map (\s -> (rules ++ [rule], s)) states

runNDepth :: (State t -> (Rule, [ReduceResult t])) -> SMTConverter ast out io -> io -> [State t] -> Config -> IO [([Rule], [Int], State t)]
runNDepth red con hpp states config = runNDepth' red $ map (\s -> (([], [], s), steps config)) states
  where
    runNDepth' :: (State t -> (Rule, [ReduceResult t])) -> [(([Rule], [Int], State t), Int)] -> IO [([Rule], [Int], State t)]
    runNDepth' _ [] = return []
    runNDepth' red' ((rss, 0):xs) = return . (:) rss =<< runNDepth' red' xs
    runNDepth' red' ((((rs, is, s), n)):xs) = do
        case logStates config of
            Just f -> outputState f rs is s
            Nothing -> return ()

        (app_rule, reduceds) <- reduce red' con hpp config s

        let isred = if length (reduceds) > 1 then zip (map Just [1..]) reduceds else zip (repeat Nothing) reduceds
        
        let mod_info = map (\(i, s') -> ((rs ++ [app_rule], is ++ maybe [] (\i' -> [i']) i, s'), n - 1)) isred
        
        runNDepth' red' (mod_info ++ xs)

runNDepthNoConstraintChecks :: [State t] -> Int -> [([Rule], State t)]
runNDepthNoConstraintChecks states d = runNDepthNCC' $ map (\s -> (([], s), d)) states
  where
    runNDepthNCC' :: [(([Rule], State t), Int)] -> [([Rule], State t)]
    runNDepthNCC' [] = []
    runNDepthNCC' ((rss, 0):xs) = rss : runNDepthNCC' xs
    runNDepthNCC' ((((rs, s), n)):xs) =
        let (app_rule, reduceds) = reduceNoConstraintChecks stdReduce undefined s
            mod_info = map (\s' -> ((rs ++ [app_rule], s'), n - 1)) reduceds
        in runNDepthNCC' (mod_info ++ xs)

outputState :: String -> [Rule] -> [Int] -> State t -> IO ()
outputState fdn rs is s = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length rs) ++ ".txt"
    let write = pprExecStateStr s ++ "\n\n" ++ show (zip ([0..] :: [Integer]) rs)
    writeFile fn write

    putStrLn fn