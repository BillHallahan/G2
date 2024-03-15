module Floats1 where

f :: Float -> Float
f x | x > 0 = x / 0
f x | x == 0 = x / x
f x | x < 0 = x / 0

{-# NOINLINE g #-}
g :: Float -> Float
g x | abs(x - 9.1) < 0.001  = x + 0.1
    | otherwise = x

gConc :: Float
gConc = g 9.1

{-# NOINLINE h #-}
h :: Float -> Float
h x = 2 * g x

hConc :: Float
hConc = h 9.1

{-# NOINLINE k #-}
k :: Float -> Float
k x | abs(x - 0.1) < 0.001  = x + 0.2
    | otherwise = x

kConc :: Float
kConc = k 0.1

showFloat1 :: Float -> String
showFloat1 x | x > 100 * 100 * 100 = "large " ++ show x
             | otherwise = show x

showFloat2 :: Float -> String
showFloat2 = show . f

m :: Float -> Float
m x | x == 9.1  = x + 0.1
    | otherwise = x

