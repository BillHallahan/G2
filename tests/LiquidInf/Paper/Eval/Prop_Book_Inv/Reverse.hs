{-@ LIQUID "--no-termination" @-}

module Reverse (reverse) where

import Prelude hiding (length, reverse)

{-@ prop_reverse :: [a] -> { v:Bool | v } @-}
prop_reverse :: [a] -> Bool
prop_reverse xs = length (reverse xs) == length xs

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

reverse xs        = go [] xs

go acc []     = acc
go acc (x:xs) = go (x:acc) xs