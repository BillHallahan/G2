module Guards where

f :: Bool -> Int
f x
    | x = 1
    | otherwise = 0

g :: Bool -> Int -> Bool
g x y = y /= 0