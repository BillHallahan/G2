module Sets2 (f) where

import Data.Set

{-@ f :: xs:[Int] -> ys:[Int] -> { zs:[Int] | listElts zs = Set_cup (listElts xs) (listElts ys) } @-}
f :: [Int] -> [Int] -> [Int]
f = g

{-@ g :: [Int] -> [Int] -> [Int] @-}
g :: [Int] -> [Int] -> [Int]
g [] ys = ys
g xs [] = xs
g (x:xs) ys = x:g xs ys
