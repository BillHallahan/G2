module Sorting where

import qualified Data.Map as M

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

g2Entry6 :: Int -> Int
g2Entry6 a = let m = M.fromList [(1, 'a'), (2, 'b')]
                 m' = M.insert a 'c' m
             in case M.lookup 1 m' of
               Just _ -> 13579
               _ -> 24680

