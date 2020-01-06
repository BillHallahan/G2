{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined where

{-@ f :: {v:Int | v == 0} @-}
f :: Int
f = g h 0

{-@ g :: (a -> a) -> a -> a @-}
g :: (a -> a) -> a -> a
g j x = j x

{-@ h :: Int -> Int @-}
h :: Int -> Int
h x = x