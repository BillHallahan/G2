-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNDepth
    , runNDepthNoConstraintChecks
    , stdReduce
    ) where

import G2.Internals.Config.Config

import G2.Internals.Execution.Reducer
import G2.Internals.Execution.Rules
import G2.Internals.Language.Support
import G2.Internals.Solver.Language
import G2.Lib.Printers

import Data.List
import System.Directory

runNDepth :: Reducer r p h t => r -> SMTConverter ast out io -> io -> p -> [State h t] -> Config -> IO [([Int], State h t)]
runNDepth red con hpp p states config = runNDepth' red p [] $ map (\s -> ([], s)) states
  where
    runNDepth' :: Reducer r p h t => r -> p -> [([Int], State h t)] -> [([Int], State h t)] -> IO [([Int], State h t)]
    runNDepth' _ _ _ [] = return []
    runNDepth' red' p' fnsh (rss@(is, s):xs)
        | stopRed red' s =
            let
                fnsh' = if true_assert s && isExecValueForm s then rss:fnsh else fnsh
                (xs', p'') = orderStates red' p' fnsh' xs
            in
            return . (:) rss =<< runNDepth' red' p'' fnsh' xs'
        | otherwise = do
            case logStates config of
                Just f -> outputState f is s
                Nothing -> return ()

            reduceds <- reduce (redRules red') con hpp config s

            let isred = if length (reduceds) > 1 then zip (map Just [1..]) reduceds else zip (repeat Nothing) reduceds
            
            let mod_info = map (\(i, s') -> (is ++ maybe [] (\i' -> [i']) i, s' {halter = stepHalter red' s'})) isred
            
            runNDepth' red' p' fnsh (mod_info ++ xs)

runNDepthNoConstraintChecks :: [State h t] -> Int -> [State h t]
runNDepthNoConstraintChecks states d = runNDepthNCC' $ map (\s -> (s, d)) states
  where
    runNDepthNCC' :: [(State h t, Int)] -> [State h t]
    runNDepthNCC' [] = []
    runNDepthNCC' ((rss, 0):xs) = rss : runNDepthNCC' xs
    runNDepthNCC' ((s, n):xs) =
        let reduceds = reduceNoConstraintChecks stdReduce undefined s
            mod_info = map (\s' -> (s', n - 1)) reduceds
        in runNDepthNCC' (mod_info ++ xs)

outputState :: String -> [Int] -> State h t -> IO ()
outputState fdn is s = do
    let dir = fdn ++ "/" ++ foldl' (\str i -> str ++ show i ++ "/") "" is
    createDirectoryIfMissing True dir

    let fn = dir ++ "state" ++ show (length $ rules s) ++ ".txt"
    let write = pprExecStateStr s
    writeFile fn write

    putStrLn fn