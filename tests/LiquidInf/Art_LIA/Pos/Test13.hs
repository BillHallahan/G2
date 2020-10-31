{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined where

{-@ die :: {v:String | false} -> a @-}
die = error

data C a = E | C a

{-@ measure isC  @-}
isC :: C a -> Int
isC E = 0
isC (C x) = 1


{-@ invariant {v:C a | 0 <= isC v} @-}
{-@ invariant {v:C a | isC v <= 1} @-}

f :: C a -> C (a, a)
f E = E
f (C x) = C (x, x)

{-@ prop_zipWith :: Num a => C a -> {v:Bool | v} @-}
prop_zipWith xs = isC xs == isC (f xs)