module DerivingSimple where

data X = A | B deriving (Eq, Ord)

eq :: X -> X -> Bool
eq x y = x == y

notEq :: X -> X -> Bool
notEq x y = x /= y

lt :: X -> X -> Bool
lt x y = x < y

gt :: X -> X -> Bool
gt x y = x > y
