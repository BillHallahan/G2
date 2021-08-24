{-@ LIQUID "--no-termination" @-}

module Sets9 (prop) where

import Data.Set

{-@ prop :: v:Int -> s1:[Int] -> { s2:[Int] | listElts s2 == Set_cup (listElts s1) (Set_sng v) } @-}
prop :: Int -> [Int] -> [Int]
prop = f

{-@ f :: Int -> [Int] -> [Int] @-}
f :: Int -> [Int] -> [Int]
f x xs = x:xs