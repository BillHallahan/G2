module Sets4 (f) where

import Data.Set

{-@ f :: xs:[Int] -> { ys:[Int] | Set_sub (listElts ys) (listElts xs) } @-}
f :: [Int] -> [Int]
f = g

{-@ g :: [Int] -> [Int] @-}
g :: [Int] -> [Int]
g [] = []
g (_:xs) = xs