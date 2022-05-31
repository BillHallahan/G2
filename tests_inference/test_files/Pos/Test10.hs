{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined where

{-@ f :: n:Nat -> a -> {v:Int | v = 2} @-}
f = g

g :: Int -> a -> Int
g n x = if n == -1 then -1 else 2

