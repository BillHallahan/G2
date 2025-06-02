module IfTest where

f :: Int -> Int -> Int
f a b =
    if a == b then
        a + b
    else
        b
