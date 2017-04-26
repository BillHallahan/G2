module HigherOrderMath where

abs2 :: Double -> Double
abs2 x
    | x >= 0 = x 
    | otherwise = 0 - x --If this 0 isn't here, error!

square :: Double -> Double
square x = x * x

fourthPower :: Double -> Double
fourthPower x = square x * square x

applyTwice :: (Double -> Double) -> Double -> Double
applyTwice f x = f (f x)

fixed :: (Double -> Double) -> Double -> Bool
fixed f x = f x == applyTwice f x

negative :: (Double -> Double) -> Double -> Bool
negative f x = f x < 0

isTrue :: Bool -> Bool
isTrue b = b