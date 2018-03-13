module Distance where

{-@ distance2 :: x:Double -> Double @-}
distance2 :: Double -> Double
distance2 x = x^(3 :: Int)

{-@ distance3 :: x:Double -> {_:Double | false} @-}
distance3 :: Double -> Double
distance3 x = x^3