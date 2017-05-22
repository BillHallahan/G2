module DataTypes where

data X = A Int | B X

f :: X -> X
f (A 0) = A 1
f (A 5) = A 2
f (B x) = x
f x = x