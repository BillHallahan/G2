module HigherOrder2 where

{-@ f :: (i:Int -> {j:Int | j > i}) -> x:Int -> { y:Int | y > x } @-}
f :: (Int -> Int) -> Int -> Int
f h i = h i

{-@ g :: x:Int -> { y:Int | y > x } @-}
g :: Int -> Int
g x = x + 1