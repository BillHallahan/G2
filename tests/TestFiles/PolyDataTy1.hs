module PolyDataTy1 where

data X a = X a | Y

f :: Int -> X Int -> Int
f _ (X x) = x
f x Y = x