module LetFloating2 where

f :: Int -> Int
f x =
    let
        g = \y -> y + 1 + h 4
        h = \y -> y + 2 + i
        i = 7
    in
    z g x

z :: (Int -> Int) -> Int -> Int
z f x = f (f x)

output32 :: Int -> Int -> Int -> Bool
output32 _ _ = (32 ==)