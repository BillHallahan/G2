module LetFloating6 where

f :: Int -> Int
f x =
    let
        {-# NOINLINE h #-}
        h = \y -> y + i
        {-# NOINLINE i #-}
        i = 7
    in
    z h x

z :: (Int -> Int) -> Int -> Int
z f x = f x

output32 :: Int -> Int -> Bool
output32 _ = (32 ==)