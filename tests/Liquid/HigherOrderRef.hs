module HigerOrderRef where

{-@ f :: (x1:Int -> {y1:Int | x1 < y1 }) -> x2:Int -> {y2:Int | x2 < y2 } @-}
f :: (Int -> Int) -> Int -> Int
f g x = g x