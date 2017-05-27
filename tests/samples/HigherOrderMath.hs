module HigherOrderMath where

abs2 :: Double -> Double
abs2 x
    | x >= 0 = x 
    | otherwise = 0 - x --If this 0 isn't here, error!

square :: Double -> Double
square x = x * x

fourthPower :: Double -> Double
fourthPower x = square x * square x

fixed :: (Double -> Double) -> Double -> Bool
fixed f x = f x == f (f x)

negative :: (Double -> Double) -> Double -> Bool
negative f x = f x < 0

add1 :: Double -> Double
add1 x = 1 + x

functionSatisfies :: ((Double -> Double) -> Bool) -> (Double -> Double) -> Double -> Double
functionSatisfies f g x = if f g then g x else x

isPositiveAt0 :: (Double -> Double) -> Bool
isPositiveAt0 f = f 0 > 0

isTrue :: (Double -> Double) -> Double -> Bool -> Bool
isTrue _ _ b = b