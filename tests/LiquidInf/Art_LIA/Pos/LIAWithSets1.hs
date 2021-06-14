module Sets1 (f) where

import Data.Set

{-@ f :: [{ y:Int | y == 0 }] -> [{ y:Int | y == 0 }] @-}
f :: [Int] -> [Int]
f = g

{-@ g :: [Int] -> [Int] @-}
g :: [Int] -> [Int]
g xs = xs