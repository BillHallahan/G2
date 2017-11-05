module PolyPred1 where

data X a = X a

intPred :: Int -> Bool
intPred x = 0 <= x

fAssert :: X Int -> Int -> Bool
fAssert (X x) y = x <= y

f :: X Int -> Int
f (X x) = x + x