module Poly3 where

{-@ f :: [{ x:Int | x > 0 }] -> [{ x:Int | x > 4 }] @-}
f :: [Int] -> [Int]
f xs = g (fil xs)

fil :: [Int] -> [Int]
fil (x:xs)
    | x > 4 = x:fil xs
    | otherwise = fil xs
fil [] = []

g :: [a] -> [a]
g x = x