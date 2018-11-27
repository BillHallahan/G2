module LetFloating3 where

f :: Int -> Int
f x =
    let
        {-# NOINLINE g #-}
        g = \y -> y + 1 + h 4
        {-# NOINLINE h #-}
        h = \y -> y + 2 + i
        {-# NOINLINE i #-}
        i = 7
    in
    z g x

z :: (Int -> Int) -> Int -> Int
z f x = f (f x)

output32 :: Int -> Int -> Bool
output32 _ = (32 ==)
