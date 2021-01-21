module Poly16 (call) where

call :: (k, Int) -> Int
call xs = 
    case f xs of
        (_, v) -> g v

f :: (k, Int) -> (k, Bool)
f (k, v) = (k, True)

{-@ g :: {b:Bool | b} -> Int @-}
g :: Bool -> Int
g _ = 1