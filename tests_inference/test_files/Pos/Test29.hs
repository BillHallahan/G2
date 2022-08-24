{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (k) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import Data.List (foldr1)

{-@ k :: k:Nat -> [{v:Int | 0 <= v && v <= 1}] -> {v:Int | 0 <= v && v <= 1 } @-}
k   :: Int -> [Int] -> Int
k k cs = n k cs

n   :: Int -> [Int] -> Int
n k cs = foldr1 (\x y -> x) cs