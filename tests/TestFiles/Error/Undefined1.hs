module Undefined1 where

undefined1 :: Int -> Int
undefined1 x = 4 + undefined

undefined2 :: Int -> Int
undefined2 x =
    case y of
        1 -> 3
        6 -> 8
        _ -> 9
    where
        y = undefined