module Combined (f) where

{-@ f :: {x:Int | 0 <= x && x <= 2 } -> { x:Int | -6 <= x && x <= 0 } @-}
f :: Int -> Int
f x = n x

n :: Int -> Int
n x
    | x == 2 = r
    | otherwise = -2

r :: Int
r = -5