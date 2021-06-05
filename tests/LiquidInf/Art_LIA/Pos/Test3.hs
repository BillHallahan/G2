-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined () where

data R = R

f :: R
f = k a

a :: Int
a = 1

{-@ k :: { v:Int | v = 1 } -> R @-}
k :: Int -> R
k p = R
