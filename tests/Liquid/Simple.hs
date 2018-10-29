module Simple where

{-@ f :: {b:Bool | b } @-}
f :: Bool
f = g

{-@ g :: {b:Bool | b } @-}
g :: Bool
g = True