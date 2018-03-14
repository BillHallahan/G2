-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNDepth
    , executeNext
    , halterIsZero
    , halterSub1
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

-- runNBreadth :: SMTConverter ast out io -> io -> [([Rule], State t)] -> Int -> IO [([Rule], State t)]
-- runNBreadth _ _ [] _ = return []
-- runNBreadth _ _ rss 0 = return rss
-- runNBreadth con hpp rss n = do
--     rss' <- return . concat =<< mapM go rss
--     runNBreadth con hpp rss' (n - 1)

--     where
--         go :: ([Rule], State t) -> IO [([Rule], State t)]
--         go (rules, state) = do
--             (rule, states) <- reduce stdReduce con hpp undefined state
--             return $ map (\s -> (rules ++ [rule], s)) states
 
-- runNBreadthNoConstraintChecks :: [([Rule], State t)] -> Int -> [([Rule], State t)]
-- runNBreadthNoConstraintChecks [] _ = []
-- runNBreadthNoConstraintChecks rss 0 = rss
-- runNBreadthNoConstraintChecks rss n = runNBreadthNoConstraintChecks (concatMap go rss) (n - 1)
--   where
--     go :: ([Rule], State t) -> [([Rule], State t)]
--     go (rules, state) = let (rule, states) = reduceNoConstraintChecks stdReduce undefined state
--                         in map (\s -> (rules ++ [rule], s)) states

runNDepth :: (State h t -> (Rule, [ReduceResult t])) -> (State h t -> Bool) -> (State h t -> h) -> (p -> [([Int], State h t)] -> [([Int], State h t)] -> [([Int], State h t)])  -> SMTConverter ast out io -> io -> p -> [State h t] -> Config -> IO [([Int], State h t)]
runNDepth red hal halR sel con hpp p states config = runNDepth' red hal halR sel p [] $ map (\s -> ([], s)) states
  where
    runNDepth' :: (State h t -> (Rule, [ReduceResult t])) -> (State h t -> Bool) -> (State h t -> h) -> (p -> [([Int], State h t)] -> [([Int], State h t)] -> [([Int], State h t)]) -> p -> [([Int], State h t)] -> [([Int], State h t)] -> IO [([Int], State h t)]
    runNDepth' _ _ _ _ _ _ [] = return []
    -- runNDepth' red' hal' sel' fnsh ((rss, 0):xs) =
    --     let
    --         fnsh' = if true_assert (snd rss) && isExecValueForm (snd rss) then rss:fnsh else fnsh
    --     in
    --     return . (:) rss =<< runNDepth' red' sel' fnsh' (sel' fnsh' xs)
    runNDepth' red' hal' halR' sel' p' fnsh (rss@(is, s):xs)
        | hal' s =
            let
                fnsh' = if true_assert s && isExecValueForm s then rss:fnsh else fnsh
            in
            return . (:) rss =<< runNDepth' red' hal' halR' sel' p' fnsh' (sel' p' fnsh' xs)
        | otherwise = do
            case logStates config of
                Just f -> outputState f is s
                Nothing -> return ()

            reduceds <- reduce red' con hpp config s

            let isred = if length (reduceds) > 1 then zip (map Just [1..]) reduceds else zip (repeat Nothing) reduceds
            
            let mod_info = map (\(i, s') -> (is ++ maybe [] (\i' -> [i']) i, s' {halter = halR' s'})) isred
            
            runNDepth' red' hal' halR' sel' p' fnsh (mod_info ++ xs)

executeNext :: p -> [([Int], State h t)] -> [([Int], State h t)] -> [([Int], State h t)]
executeNext _ _ xs = xs

halterSub1 :: State Int t -> Int
halterSub1 (State {halter = h}) = h - 1

halterIsZero :: State Int t -> Bool
halterIsZero (State {halter = 0}) = True
halterIsZero _ = False

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