module F3 where

{-@ f3 :: x:[Int] -> {v:[Int] | v < x} @-}
f3 :: [Int] -> [Int]
f3 x = g3 [0, 1]

{-# NOINLINE g3 #-}
g3 :: a -> a
g3 x = x
