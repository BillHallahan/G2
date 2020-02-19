{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined () where

data R = R
data Assocs = Assocs R

f :: R
f = k g a

g :: Assocs
g = Assocs (i $ i R) 

i :: R -> R
i x = x

a :: Int
a = 1

{-@ k :: Assocs -> { v:Int | v = 1 } -> R @-}
k :: Assocs -> Int -> R
k (Assocs _) p = R