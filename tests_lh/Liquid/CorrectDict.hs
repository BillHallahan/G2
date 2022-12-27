module CorrectDict where

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ divide :: Double -> {v:Double | v /= 0}-> Double @-}
divide :: Double -> Double -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / d

{-@ f :: x:Int -> { y:Int | y > x } @-}
f :: Int -> Int
f x = g x

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = x + 4