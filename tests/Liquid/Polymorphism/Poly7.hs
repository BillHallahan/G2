module Poly7 where

data C a = E | C a

f :: C a -> C (a, a)
f E = E
f (C x) = C (x, x)

{-@ prop_f :: C Int -> {v:Bool | v} @-}
prop_f :: C Int -> Bool
prop_f c = case c of { E -> 0; C _ -> 1 } == case f c of { E -> 0; C _ -> 1 }