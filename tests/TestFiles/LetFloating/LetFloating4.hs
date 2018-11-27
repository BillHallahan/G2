module LetFloating4 where

f :: Int -> Int
f x =
    let
        {-# NOINLINE g #-}
        g = \y -> y + 1
    in
    z g x

z :: (Int -> Int) -> Int -> Int
z f x = f x

output12 :: Int -> Int -> Bool
output12 _ = (12 ==)
