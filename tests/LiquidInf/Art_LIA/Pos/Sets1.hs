module Sets1 (f) where

import Data.Set

{-@ f :: xs:[Int] -> { ys:[Int] | listElts ys = listElts xs } @-}
f :: [Int] -> [Int]
f = g

{-@ g :: [Int] -> [Int] @-}
g :: [Int] -> [Int]
g xs = xs