module HigherOrderMath where

abs2 :: Float -> Float
abs2 x
    | x >= 0 = x 
    | otherwise = -x

abs3 :: Float -> Float
abs3 = abs

square :: Float -> Float
square x = x * x

negativeSquare :: Float -> Float
negativeSquare x = -(square x)

fourthPower :: Float -> Float
fourthPower x = square x * square x

fixed :: (Float -> Float) -> Float -> Bool
fixed f x = x == (f x)

negative :: (Float -> Float) -> Float -> Bool
negative f x = f x < 0

add1 :: Float -> Float
add1 x = 1 + x

sub1 :: Float -> Float
sub1 x = x - 1

add :: Float -> Float -> Float
add x y = x + y

sub :: Float -> Float -> Float
sub x y = x - y

pythagorean :: Float -> Float -> Float
pythagorean a b = approxSqrt (a * a + b * b) 0.01

-- Computes the square root of x to a precision of at least e
-- using the Babylonian method
approxSqrt :: Float -> Float -> Float
approxSqrt x eAllowed = bab x (x / 4) eAllowed
    where
        bab :: Float -> Float -> Float -> Float
        bab orig x eAllowed =
            let
                guess = ((orig / x) + x) / 2
                e = abs2((orig - guess * guess) / (2 * guess))--err orig guess
            in
            if e <= eAllowed then guess else bab orig guess eAllowed

        --Calculate the error
        err :: Float -> Float -> Float
        err orig guess = abs2((orig - guess * guess) / (2 * guess))

sameFloatArgLarger :: (Float -> Float -> Float) -> Float -> Bool
sameFloatArgLarger f x = f x x > x

functionSatisfies :: ((Float -> Float) -> Bool) -> (Float -> Float) -> Float -> Float
functionSatisfies f g x = if f g then g x else x

notNegativeAt0 :: (Float -> Float) -> Bool
notNegativeAt0 f = f 0 >= 0

notNegativeAt0NegativeAt1 :: (Float -> Float) -> Bool
notNegativeAt0NegativeAt1 f =
    let
        at0 = notNegativeAt0 f
        at1 = f 1
    in
    at0 && at1 < 0

isTrue0 :: (Float -> Float) -> Bool -> Bool
isTrue0 _ b = b

isTrue1 :: (Float -> Float) -> Float -> Bool -> Bool
isTrue1 _ _ b = b

isTrue2 :: (Float -> Float -> Float) -> Float -> Bool -> Bool
isTrue2 _ _ b = b