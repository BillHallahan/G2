module Sets5 (f) where

import Data.Set

{-@ f :: x:Int -> [Int] -> { ys:[Int] | Set_mem x (listElts ys) } @-}
f :: Int -> [Int] -> [Int]
f = g

{-@ g :: Int -> [Int] -> [Int] @-}
g :: Int -> [Int] -> [Int]
g x xs = x:xs