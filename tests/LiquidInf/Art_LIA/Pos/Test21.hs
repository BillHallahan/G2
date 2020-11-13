{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import qualified Data.Map as M
import Data.List (minimumBy)

{-@ f :: [Int] -> {v: Int | v = 1} @-}
f :: [Int] -> Int
f cs = g (h cs)

g :: Int -> Int
g _ = 1

h :: [Int] -> Int
h cs = minimumBy (\_ _ -> LT) cs