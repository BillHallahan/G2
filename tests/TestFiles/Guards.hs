module Guards where

f :: Int -> Int
f x
    | x > 100 = x
    | otherwise = x

g :: Int -> Int -> Bool
g x y = x <= 100 && y /= 91