module PolyTypes where

polyFst :: a -> b -> a
polyFst a b = a

typedFst :: Int -> String -> Int
typedFst a b = polyFst a b

