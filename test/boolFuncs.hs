module BoolFuncs where

data X = A | B | C X

getB :: X -> X
getB x = case hasB x of
    True -> B
    False -> A

hasB :: X -> Bool
hasB A = False
hasB B = True
hasB (C x) = hasB x