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

runNDepth :: (Reducer r t, Halter h hv t, Orderer or orv t) => r -> h -> or -> SMTConverter ast out io -> io -> orv -> [State hv t] -> Config -> IO [([Int], State hv t)]
runNDepth red hal ord con hpp p states config = runNDepth' red hal ord p [] $ map (\s -> ([], s)) states
  where
    runNDepth' :: (Reducer r t, Halter h hv t, Orderer or orv t) => r -> h -> or -> orv -> [([Int], State hv t)] -> [([Int], State hv t)] -> IO [([Int], State hv t)]
    runNDepth' _ _ _ _ _ [] = return []
    runNDepth' red' hal' ord' p' fnsh (rss@(is, s):xs)
        | hc == Accept =
            let
                fnsh' = rss:fnsh
                (xs', p'') = orderStates ord' p' fnsh' xs
            in
            return . (:) rss =<< runNDepth' red' hal' ord' p'' fnsh' xs'
        | hc == Discard =
            let
                (xs', p'') = orderStates ord' p' fnsh xs
            in
            runNDepth' red' hal' ord' p'' fnsh xs'
        | hc == Switch =
            let
                (xs', p'') = orderStates ord' p' fnsh (rss:xs)
            in
            runNDepth' red' hal' ord' p'' fnsh xs'
        | otherwise = do
            case logStates config of
                Just f -> outputState f is s
                Nothing -> return ()

            reduceds <- reduce (redRules red') con hpp config s

            let isred = if length (reduceds) > 1 then zip (map Just [1..]) reduceds else zip (repeat Nothing) reduceds
            
            let mod_info = map (\(i, s') -> (is ++ maybe [] (\i' -> [i']) i, s' {halter = stepHalter hal' s'})) isred
            
            runNDepth' red' hal' ord' p' fnsh (mod_info ++ xs)
        where
            hc = stopRed hal' s

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