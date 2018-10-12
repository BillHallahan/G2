module PolyTypes where

polyFst :: a -> b -> a
polyFst a b = a

typedFst :: Int -> Double -> Int
typedFst a b = polyFst a b

