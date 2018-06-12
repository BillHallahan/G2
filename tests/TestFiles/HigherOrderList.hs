module HigherOrderList where

g :: [Int -> Int] -> Int -> [Int]
g [] _ = []
g (f:fs) x = f x:g fs x