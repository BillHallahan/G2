-- cmd_line = (--no-keep_quals)

module Double () where

{-@ f :: x:Double -> { y:Double | y > x } @-}
f :: Double -> Double
f x = g (a x)

g :: Double -> Double
g x
    | x >= 0 = x + 1
    | otherwise = x - 1

a :: Double -> Double
a x
    | x >= 0 = x
    | otherwise = 0 - x