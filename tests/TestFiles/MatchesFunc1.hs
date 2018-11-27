module MultiSplit2 where

data X = X Int X | Y

f :: Int -> Int
f x = x + g x0

g :: X -> Int
g (X x Y) = x
g (X x y) = x + g y
g Y = 0

x0 :: X
x0 = X 0 x1

x1 :: X
x1 = X 1 x2

x2 :: X
x2 = X 2 x3

x3 :: X
x3 = X 3 Y
