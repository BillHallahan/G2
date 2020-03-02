module Double () where

{-@ f :: x:Double -> { y:Double | y >= x } @-}
f :: Double -> Double
f x = g x

g :: Double -> Double
g x
    | x >= 0 = x
    | otherwise = 0 - x