module LetFloating where

f :: Int -> Int
f x =
    let
        {-# NOINLINE y #-}
        y = \p -> p
    in
    y x

output6 :: Int -> Int -> Int -> Bool
output6 _ _ x = (6 == x)