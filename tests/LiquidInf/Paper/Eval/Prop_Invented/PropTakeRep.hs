{-@ LIQUID "--no-termination" @-}

module TakeRep (prop_take_rep) where

import Prelude hiding (length, take, replicate)

{-@ prop_take_rep :: n:Nat -> { k:Int | k >= n } -> Int -> { v:Bool | v } @-}
prop_take_rep :: Int -> Int -> Int -> Bool
prop_take_rep n k x = length (take n (replicate k x)) == n 

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

take :: Int -> [a] -> [a]
take 0 _      = []
take n (x:xs) = x : take (n-1) xs
take _ _      = die "won't happen"

empty = []

replicate :: Int -> a -> [a]
replicate n x
  | n == 0    = empty
  | otherwise = x:replicate (n - 1) x

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
