module Defunc1 where

data A = A (Int -> Int)
       | B Int

f :: A -> A
f (A g) = B (g 2)
f x = x

h :: (Int -> Int) -> Int
h fg = fg 0

add1 :: Int -> Int
add1 x = x + 1

multiply2 :: Int -> Int
multiply2 x = x * 2

data X = X (Int -> Int)

x :: X -> Int
x (X g) = g 4

data Y a = Y a

mapY :: (a -> a) -> Y a -> Y a
mapY f (Y x) = Y (f x)

yAdd1 :: Y Int -> Y Int
yAdd1 (Y x) = Y (x + 1)

mapYInt :: (Y Int -> Y Int) -> Y Int -> Y Int
mapYInt f x = f x 