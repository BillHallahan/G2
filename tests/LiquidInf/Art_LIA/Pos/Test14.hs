{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined ( L
                , size
                , e2) where

data L a = E | L a

{-@ measure size @-}
size :: L a -> Int
size E = 0
size (L x) = 1


{-@ invariant {v:L a | 0 <= size v} @-}
{-@ invariant {v:L a | size v <= 1} @-}

{-@ e2 :: {xs:L Int | size xs == 0 } @-}
e2 = e

e = E :: L Int