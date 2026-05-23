{-# LANGUAGE CPP, MultiWayIf #-}

module Seq1 where

import Data.List

con :: Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
con x xs ys = if x > 10 then xs ++ ys else ys ++ xs

listLen :: [(Int, Int)] -> (Int, Bool)
listLen xs = let l = length xs in (l, case l > 5 of True -> False; False -> True)

listLen2 :: [(Double, Float)] -> (Int, Bool)
listLen2 s =
    case s of
        (c:s) ->
            let l = length (c:s) in
            if l > 4 then (l, True) else (l, False)
        [] -> (1000, False)
    
listLen3 :: (Int, Double) -> [(Int, Double)] -> (Int, Bool)
listLen3 c s =
    let l = length (c:s) in
    if l > 4 then (l, True) else (l, False)

listApp :: [(Int, Int)] -> [(Int, Int)] -> Int
listApp xs ys = let cs = xs ++ ys in
                if | cs == [(1, 2), (3, 4), (5, 6)] -> 2
                   | cs == [(6, 5), (4, 3)] -> 1
                   | otherwise -> 0

take1 :: [(Int, Int)] -> (Bool, [(Int, Int)])
take1 str = case t == [(1, 2), (3, 4), (5, 6), (7, 8), (9, 10)] of
                True -> (False, t)
                False -> (True, t)
    where
        t = take 5 str
