module Poly2 where

{-@ f :: [{ x:Int | x > 0 }] -> [{ x:Int | x > 0 }] @-}
f :: [Int] -> [Int]
f x = g x

g :: [a] -> [a]
g x = x