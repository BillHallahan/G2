module HigherOrderMath where

abs2 :: Double -> Double
abs2 x
    | x >= 0 = x 
    | otherwise = 0 - x --If this 0 isn't here, error!

-- square :: Double -> Double
-- square x = x * x

-- negativeSquare :: Double -> Double
-- negativeSquare x = 0 - square x

-- fourthPower :: Double -> Double
-- fourthPower x = square x * square x

fixed :: (Double -> Double) -> Double -> Bool
fixed f x = x == (f x)

negative :: (Double -> Double) -> Double -> Bool
negative f x = f x < 0

add1 :: Double -> Double
add1 x = 1 + x

sub1 :: Double -> Double
sub1 x = x - 1

add :: Double -> Double -> Double
add x y = x + y

sub :: Double -> Double -> Double
sub x y = x - y

pythagorean :: Double -> Double -> Double
pythagorean a b = approxSqrt (a * a + b * b) 0.01

-- Computes the square root of x to a precision of at least e
-- using the Babylonian method
approxSqrt :: Double -> Double -> Double
approxSqrt x eAllowed = bab x (x / 4) eAllowed
    where
        bab :: Double -> Double -> Double -> Double
        bab orig x eAllowed =
            let
                guess = ((orig / x) + x) / 2
                e = abs2((orig - guess * guess) / (2 * guess))--err orig guess
            in
            if e <= eAllowed then guess else bab orig guess eAllowed

        --Calculate the error
        err :: Double -> Double -> Double
        err orig guess = abs2((orig - guess * guess) / (2 * guess))

sameDoubleArgLarger :: (Double -> Double -> Double) -> Double -> Bool
sameDoubleArgLarger f x = f x x > x

functionSatisfies :: ((Double -> Double) -> Bool) -> (Double -> Double) -> Double -> Double
functionSatisfies f g x = if f g then g x else x

notNegativeAt0 :: (Double -> Double) -> Bool
notNegativeAt0 f = f 0 >= 0

notNegativeAt0NegativeAt1 :: (Double -> Double) -> Bool
notNegativeAt0NegativeAt1 f =
    let
        at0 = notNegativeAt0 f
        at1 = f 1
    in
    at0 && at1 < 0

isTrue0 :: (Double -> Double) -> Bool -> Bool
isTrue0 _ b = b

isTrue1 :: (Double -> Double) -> Double -> Bool -> Bool
isTrue1 _ _ b = b

isTrue2 :: (Double -> Double -> Double) -> Double -> Bool -> Bool
isTrue2 _ _ b = b
