module Divide (divide) where

{-@ divide :: Int -> Double @-}
divide :: Int -> Double
divide d = 1.0 / fromIntegral d