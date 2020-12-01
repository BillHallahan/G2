{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (k) where

import Data.List (minimumBy)

{-@ k :: [({v:Int | 0 <= v }, Double)] -> {v:Int | 0 <= v } @-}
k :: [(Int, Double)] -> Int
k cs = n cs

n :: [(Int, Double)] -> Int
n cs = fst $ minimumBy (\_ _ -> LT) cs