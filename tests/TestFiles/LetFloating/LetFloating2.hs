module LetFloating2 where

f :: Int -> Int
f x =
    let
        {-# NOINLINE g #-}
        g = \y -> y + 1
    in
    g x

output16 :: Int -> Int -> Bool
output16 _ = (16 ==)
