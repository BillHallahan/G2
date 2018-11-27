module Case2 where

data X = A X | B

f :: X -> X
f (A _) = B
f B = A B
