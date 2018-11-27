module DerivingComp where

data X = A Int | B X deriving (Eq, Ord)

data Y = C X | D Y deriving (Eq, Ord)

eq :: Y -> Y -> Bool
eq x y = x == y

notEq :: Y -> Y -> Bool
notEq x y = x /= y

lt :: Y -> Y -> Bool
lt x y = x < y

gt :: Y -> Y -> Bool
gt x y = x > y
