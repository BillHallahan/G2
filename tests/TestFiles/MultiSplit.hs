-- This is to check that, if we look at the arguments to the same
-- ADT constructor in two different places, you get the same results

module MultiSplit1 where

data X = X Int Int

equals1 :: X -> Int -> Bool
equals1 _ x = x == 1

f :: X -> Int
f x = g x + g x

g :: X -> Int
g (X 0 0) = 0
g _ = 1
