{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where

import Data.List (minimumBy)

{-@ f :: [Int] -> {v: Int | v = 1} @-}
f :: [Int] -> Int
f cs = g (h cs)

g :: Int -> Int
g _ = 1

h :: [Int] -> Int
h cs = minimumBy (\_ _ -> LT) cs