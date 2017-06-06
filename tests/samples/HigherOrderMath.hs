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

-- power :: Double -> Int -> Double
-- power x y
--     | y == 0 = 1
--     | y > 0 = x * power x (y - 1)
--     | otherwise = 1 / (power x (0 - y))

pythagorean :: Double -> Double -> Double
pythagorean a b = approxSqrt (a * a + b * b) 0.01

--Computes the square root of x to a precision of at least e
-- using the Babylonian method
approxSqrt :: Double -> Double -> Double
approxSqrt x eAllowed = bab x (x / 4) eAllowed

--HELPERS FOR approxSqrt
-- starting :: Double -> Int -> Double
-- starting x y
--     | x > 100 = starting (x / 100) (y + 1)
--     | x < 10 = 2 * (10 `power` (y / 2))
--     | otherwise = 6 * (10 `power` (y / 2))

bab :: Double -> Double -> Double -> Double
bab orig x eAllowed =
    let
        guess = ((orig / x) + x) / 2
        e = err orig guess
    in
    if e <= eAllowed then guess else bab orig guess eAllowed

--Calculate the error
err :: Double -> Double -> Double
err orig guess = abs2((orig - guess * guess) / (2 * guess))
--END OF HELPERS FOR approxSqrt

sameDoubleArgLarger :: (Double -> Double -> Double) -> Double -> Bool
sameDoubleArgLarger f x = f x x > x

functionSatisfies :: ((Double -> Double) -> Bool) -> (Double -> Double) -> Double -> Double
functionSatisfies f g x = if f g then g x else x

isPositiveAt0 :: (Double -> Double) -> Bool
isPositiveAt0 f = f 0 > 0

isTrue :: (Double -> Double) -> Double -> Bool -> Bool
isTrue _ _ b = b

isTrue2 :: (Double -> Double -> Double) -> Double -> Bool -> Bool
isTrue2 _ _ b = b