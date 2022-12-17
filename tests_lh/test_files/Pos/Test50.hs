module Test50 (prop) where

import Prelude hiding (length, zip)

{-@ prop :: [a] -> { v:Bool | v } @-}
prop xs =
    let rs = walk xs xs in
    length rs == length xs

{-@ length :: [a] -> Int @-}
length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

walk :: [a] -> [b] -> [a]
walk (a:as) (b:bs) = a : walk as bs
walk _ _          = []