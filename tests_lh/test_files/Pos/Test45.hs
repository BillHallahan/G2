module Test44 (m) where

{-@ type TRUE = {v:Bool | v} @-}

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert _  a = a

d :: Int -> Int
d y = assert (y /= 0) 1

m :: Int -> Int
m n = d 1