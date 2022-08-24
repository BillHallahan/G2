{-@ LIQUID "--no-termination" @-}

module Test39 (f) where

empty = []

{-@ f :: {xs : [a] | (len xs == 0)} @-}
f :: [a]
f = empty
