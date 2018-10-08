module Ordering where

data X = X | Y

{-@ f :: x:X -> { y:X | x == y } @-}
f :: X -> X
f X = X
f Y = Y