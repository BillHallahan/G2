module Infinite where

f :: Int -> Int
f x
    | x > 100 = x
    | otherwise = f (x + 11)

g :: Int -> Int -> Bool
g x y = x <= 100 && y /= 91