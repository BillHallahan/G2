{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Doubles1 where

newtype NaNEq = D { unD :: Double } deriving (Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

instance Eq NaNEq where
    D f1 == D f2 | isNaN f1, isNaN f2 = True
                 | otherwise = f1 == f2

infinite :: NaNEq -> NaNEq
infinite x | x > 0 = x / 0
           | x == 0 = x / x
           | otherwise = x / 0

data Zero = PosZ | NegZ | NA deriving (Eq, Show)

zero :: NaNEq -> (NaNEq, Zero)
zero x | x == 0 && not (isNegativeZero x) = (x, PosZ)
       | x == -0 = (x, NegZ)
       | otherwise = (x, NA)

{-# NOINLINE f #-}
f :: NaNEq -> NaNEq
f x | abs(x - 9.1) < 0.001  = x + 0.1
    | otherwise = x

fConc :: NaNEq
fConc = f 9.1

{-# NOINLINE g #-}
g :: NaNEq -> NaNEq
g x = 2 * f x

gConc :: NaNEq
gConc = g 9.1

{-# NOINLINE k #-}
k :: NaNEq -> NaNEq
k x | abs(x - 0.1) < 0.001  = x + 0.2
    | otherwise = x

kConc :: NaNEq
kConc = k 0.1

m :: NaNEq -> NaNEq
m x | x == 9.1  = x + 0.1
    | otherwise = x

n :: NaNEq -> NaNEq -> (NaNEq, NaNEq)
n x y | x > y = (x * y, x / y)
      | otherwise = (sqrt x, sqrt y)

sqrtSquared :: NaNEq -> (Bool, NaNEq, NaNEq)
sqrtSquared x | sqrt x * sqrt x == x = (True, x, sqrt x * sqrt x)
              | otherwise  = (False, x, sqrt x * sqrt x)

floorAndCeiling :: NaNEq -> (Int, Int, Int)
floorAndCeiling (D x)
    | isNaN x || isInfinite x = (0, 0, 0)
    | x > 11 = (1, floor x, ceiling x)
    | x < -4 = (2, floor x, ceiling x)
    | otherwise =  (3, floor x, ceiling x)

roundTest :: NaNEq -> (Int, Int)
roundTest (D x) | isNaN x || isInfinite x = (0, 0)
                | x > 1000 || x < -1000 = (0, 0)
                | r > 10 && r < 20 = (1, r)
                | r < -10 && r > -100 = (2, r)
                | otherwise = (3, r)
    where
        r = round x

decodeFloatTest :: NaNEq -> (Int, (Integer, Int))
decodeFloatTest (D x) | isNaN x || isInfinite x = (0, (0, 0))
                      | isDenormalized x = (1, decodeFloat x)
                      | x > 1000 = (2, decodeFloat x)
                      | x > 100 = (3, decodeFloat x)
                      | x > 9 = (4, decodeFloat x)
                      | x > 4 = (5, decodeFloat x)
                      | x > 1 = (6, decodeFloat x)
                      | x > 0.5 = (7, decodeFloat x)
                      | x > 0 = (8, decodeFloat x)
                      | x == 0 = (9, decodeFloat x)
                      | x > -1 = (10, decodeFloat x)
                      | x < -5000 = (11, decodeFloat x)
                      | x < -1000 = (12, decodeFloat x)
                      | x < -100 = (13, decodeFloat x)
                      | x < -12 = (14, decodeFloat x)
                      | x < -3 = (15, decodeFloat x)
                      | otherwise = (16, decodeFloat x)

decodeFloatConst :: [(Integer, Int)]
decodeFloatConst = map decodeFloat ([-10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
                                       0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Double])

decodeFloatCheck :: NaNEq -> Int
decodeFloatCheck (D x) = case decodeFloat x of
                            (m, n) | m - 7 == 5439284022607872 -> 10
                            _ -> 20

exponentTest :: NaNEq -> (Integer, Int)
exponentTest (D x)
    | isNaN x || isInfinite x = (0, 0)
    | r > 17 = (1, r)
    | r > 4 = (2, r)
    | x < -3 = (3, r)
    | x < -17 = (4, r)
    | x < -400 = (5, r)
    | otherwise = (6, r)
    where
        r = exponent x