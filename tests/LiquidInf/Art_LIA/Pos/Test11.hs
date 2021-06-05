{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined where

{-@ f :: (Int -> Int) -> xa : Int -> { xb : Int | xa = xb } @-}
f :: (Int -> Int) -> Int -> Int
f = g

g :: (Int -> Int) -> Int -> Int
g _ x = x

