module Case2 where

data X = A X | B | C

f :: X -> X
f (A B) = A C
f B = C
f C = A (A B)
f _ = A B
