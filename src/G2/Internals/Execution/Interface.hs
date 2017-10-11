-- | Interface
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Execution.Interface
    ( runNBreadth
    , runNBreadthHist
    , runNDepth
    , runNDepthHist
    , runNDepthHist'
    , runNDepthCatchError) where

import G2.Internals.Execution.Rules
import G2.Internals.Language.Support

runNBreadth :: [State] -> Int -> [State]
runNBreadth [] _ = []
runNBreadth states 0 = states
runNBreadth states n = runNBreadth (concatMap (snd . reduce) states) (n - 1)

runNBreadthHist :: [([Rule], State)] -> Int -> [([Rule], State)]
runNBreadthHist [] _ = []
runNBreadthHist rss 0 = rss
runNBreadthHist rss n = runNBreadthHist (concatMap go rss) (n - 1)
  where
    go :: ([Rule], State) -> [([Rule], State)]
    go (rules, state) = let (rule, states) = reduce state
                        in map (\s -> (rules ++ [rule], s)) states

runNDepth :: [State] -> Int -> [State]
runNDepth states depth = runNDepth' (map (\s' -> (s', depth)) states)
    where
        runNDepth' :: [(State, Int)] -> [State]
        runNDepth' [] = []
        runNDepth' ((s, 0):xs) = s:runNDepth' xs
        runNDepth' ((s, n):xs) =
            let
                (_, red) = reduce $ s
                s'' = map (\s' -> (s', n - 1)) red
            in
            runNDepth' (s'' ++ xs)

runNDepthHist :: [State] -> Int -> [[(Maybe Rule, State)]]
runNDepthHist states d = runNDepth' (map (\s' -> ([(Nothing, s')], d)) states)
    where
        runNDepth' :: [([(Maybe Rule, State)], Int)] -> [[(Maybe Rule, State)]]
        runNDepth' [] = []
        runNDepth' ((rss, 0):xs) = rss:runNDepth' xs
        runNDepth' ((rss@((_, s):_), n):xs) =
            let
                (r', red) = reduce $ s
                s'' = map (\s' -> ((Just r', s'):rss, n - 1)) red
            in
            runNDepth' (s'' ++ xs)

runNDepthHist' :: [State] -> Int -> [([Rule], State)]
runNDepthHist' states d = runNDepth' $ map (\s -> (([], s), d)) states
  where
    runNDepth' :: [(([Rule], State), Int)] -> [([Rule], State)]
    runNDepth' [] = []
    runNDepth' ((rss, 0):xs) = rss : runNDepth' xs
    runNDepth' ((((rs, s), n)):xs) =
        let (app_rule, reduceds) = reduce s
            mod_info = map (\s' -> ((rs ++ [app_rule], s'), n - 1)) reduceds
        in runNDepth' (mod_info ++ xs)

runNDepthCatchError :: [State] -> Int -> Either [State] State
runNDepthCatchError states d = runNDepth' (map (\s' -> (s', d)) states)
    where
        runNDepth' :: [(State, Int)] -> Either [State] State
        runNDepth' [] = Left []
        runNDepth' ((s, 0):xs) =
            case runNDepth' xs of
                Left xs' -> Left (s:xs')
                Right x -> Right x
        runNDepth' ((s, n):xs) =
            let
                (r, red) = reduce $ s
                s'' = map (\s' -> (s', n - 1)) red
            in
            if r == RuleError then Right s else runNDepth' (s'' ++ xs)