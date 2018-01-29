module HigherOrder where

data X = X

f :: X -> X
f X = X

{-@ g :: (X -> X) -> {x:X | isX x} @-}
g :: (X -> X) -> X
g h = h X

{-@ measure isX @-}
isX :: X -> Bool
isX X = False