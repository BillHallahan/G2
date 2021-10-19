{-@ LIQUID "--no-termination" @-}

module PropRep (prop_rep) where

import Prelude hiding (length, take, replicate)

{-@ prop_rep :: n:Nat -> { k:Int | k >= n } -> Int -> { v:Bool | v } @-}
prop_rep :: Int -> Int -> Int -> Bool
prop_rep n k x = length (replicate n x) == n 

{-@ length :: xs:[a] -> {r : Int | (r >= -1)} @-}
length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

replicate :: Int -> a -> [a]
replicate n x
  | n == 0    = []
  | otherwise = x:replicate (n - 1) x