module Incr where

{-@ incr3 :: x:Int -> { y:Int | y == x + 3 } @-}
incr3 :: Int -> Int
incr3 x = incr2 (incr x)

{-@ incr2 :: x:Int -> { y:Int | y == x + 2 } @-}
incr2 :: Int -> Int
incr2 x = x + 2

{-@ incr :: x:Int -> { y:Int | y > x } @-}
incr :: Int -> Int
incr x = x + 1
