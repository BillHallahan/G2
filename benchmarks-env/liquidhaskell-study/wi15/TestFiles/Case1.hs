module Case1 where

data X = A | B | C

f :: Int -> X
f x
    | x < 0 = A
    | x < -1 = B
    | otherwise = C