{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE MagicHash #-}

module Divide () where

import GHC.Exts

{-@ f :: Double -> Double @-}
f :: Double -> Double
f x = g x

{-@ g :: {v:Double | v /= 0} -> Double @-}
g :: Double -> Double
g 0 = 0
g d = 1 / d