module Sorting where

g2Entry :: Int -> Int
g2Entry a = maximum (map (+1) [1, 2, a, 4, 5])

g2Entry2 :: Int -> Int
g2Entry2 a = minimum [1, 2, 3]


g2Entry3 :: Int -> Int
g2Entry3 a = foldr (+) 0 [1, a, 3]

g2Entry4 :: Int -> Int
g2Entry4 a = foldr (+) 4 [1, a, 3, 4, 5]

g2Entry5 :: [Int] -> Int
g2Entry5 xs = head $ tail xs

