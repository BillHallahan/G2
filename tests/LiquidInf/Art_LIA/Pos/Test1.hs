-- cmd_line = (--no-keep-quals)

module Test30 where

{-@ f :: x:Int -> { y:Int | y > x } @-}
f :: Int -> Int
f x = g (a x)

-- {-@ g :: x:Int -> { y:Int | y > x } @-}
g :: Int -> Int
g x = x + 1

-- {-@ a :: x:Int -> { y:Int | y >= x } @-}
-- {-@ a :: x:Int -> { y:Int | -x + y >= 0 } @-}
a :: Int -> Int
a x
    | x >= 0 = x
    | otherwise = 0 - x
