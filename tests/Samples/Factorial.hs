module Factorial where

fact :: Int -> Int
fact n =
    if n == 0
        then 1
        else n * fact (n - 1)


factIs120 :: Int -> Bool
factIs120 n =
    if fact n - 120 == 0
        then False
        else True

factIs121 :: Int -> Bool
factIs121 n =
    if fact n - 121 == 0
        then False
        else True