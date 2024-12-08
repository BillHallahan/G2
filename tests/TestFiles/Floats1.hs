{-# LANGUAGE GeneralizedNewtypeDeriving, MultiWayIf #-}

module Floats1 where

newtype NaNEq = F { unF :: Float } deriving (Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat, Show)

instance Eq NaNEq where
    F f1 == F f2 | isNaN f1, isNaN f2 = True
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
floorAndCeiling (F x)
    | isNaN x || isInfinite x = (0, 0, 0)
    | x > 11 = (1, floor x, ceiling x)
    | x < -4 = (2, floor x, ceiling x)
    | otherwise =  (3, floor x, ceiling x)

roundTest :: NaNEq -> (Integer, Integer)
roundTest (F x) | isNaN x || isInfinite x = (0, 0)
                | x > 1000 || x < -1000 = (0, 0)
                | r > 10 && r < 20 = (1, r)
                | r < -10 && r > -100 = (2, r)
                | otherwise = (3, r)
    where
        r = round x

decodeFloatTest1 :: NaNEq -> (Int, (Integer, Int))
decodeFloatTest1 (F x) | isNaN x || isInfinite x = (0, (0, 0))
                       | isDenormalized x = (1, decodeFloat x)
                       | x > 1000 = (2, decodeFloat x)
                       | x > 100 = (3, decodeFloat x)
                       | x > 9 = (4, decodeFloat x)
                       | x > 4 = (5, decodeFloat x)
                       | x > 1 = (6, decodeFloat x)
                       | x > 0.5 = (7, decodeFloat x)
                       | x > 0 = (8, decodeFloat x)
                       | x == 0 = (9, decodeFloat x)
                       | otherwise = (10, decodeFloat x)

decodeFloatTest2 :: NaNEq -> (Int, (Integer, Int))
decodeFloatTest2 (F x) | isNaN x || isInfinite x = (0, (0, 0))
                       | x > -1 = (1, decodeFloat x)
                       | x < -5000 = (2, decodeFloat x)
                       | x < -1000 = (3, decodeFloat x)
                       | x < -100 = (4, decodeFloat x)
                       | x < -12 = (5, decodeFloat x)
                       | x < -3 = (6, decodeFloat x)
                       | otherwise = (7, decodeFloat x)

decodeFloatTest3 :: NaNEq -> NaNEq
decodeFloatTest3 (F x) | -1.93e-43 <= x, x <= -1.92e-43 = F (uncurry encodeFloat (decodeFloat x))
                       | otherwise = F 0

decodeFloatConst :: [(Integer, Int)]
decodeFloatConst = map decodeFloat ([-10, -9, -8, -7, -6, -5, -4, -3, -2, -1,
                                       0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :: [Float])

decodeFloatCheck :: NaNEq -> Int
decodeFloatCheck (F x) = case decodeFloat x of
                            (m, n) | m - 7 == 10131456 -> 10
                            _ -> 20

exponentTest :: NaNEq -> (Integer, Int)
exponentTest (F x)
    | isNaN x || isInfinite x = (0, 0)
    | r > 17 = (1, r)
    | r > 4 = (2, r)
    | x < -3 = (3, r)
    | x < -17 = (4, r)
    | x < -400 = (5, r)
    | otherwise = (6, r)
    where
        r = exponent x

encodeFloatTest1 :: Integer -> Int -> (Int, Int, NaNEq)
encodeFloatTest1 x y | x > 1000 * 1000 * 10 = (-1, b, r')
                     | x > 1000 * 1000 = (0, b, r')
                     | x > 1000 = (1, b, r')
                     | x > 10 = (2, b, r')
                     | x > 1 = (3, b, r')
                     | x > -100 = (4, b, r')
                     | x > -1000 = (5, b, r')
                     | x > -1000 * 1000 = (6, b, r')
                     | x > -1000 * 1000 * 10 = (7, b, r')
                     | otherwise = (8, b, r')
    where
        r = encodeFloat x y
        r' = F r

        b = if | y == -127 -> 0
               | y > 128 -> 1
               | y > 100 -> 2
               | y > 10 -> 3
               | y > -10 -> 4
               | y > -50 -> 5
               | y > -100 -> 6
               | y > -128 -> 7
               | y > -160 -> 8
               | y > -180 -> 9
               | otherwise -> 10

significandTest :: NaNEq -> (Integer, NaNEq)
significandTest (F x)
    | isNaN x || isInfinite x = (0, 0)
    | x > 20 = (1, r)
    | x > 9 = (2, r)
    | x < -3 = (3, r)
    | x < -17 = (4, r)
    | x < -400 = (5, r)
    | r > 17 = (6, r)
    | r > 4 = (7, r)
    | otherwise = (6, r)
    where
        r = F (significand x)

scaleFloatTest :: NaNEq -> (Int, NaNEq, NaNEq)
scaleFloatTest (F x) | x > 10 = (0, F (scaleFloat 4 x), F (scaleFloat 8 x))
                     | x < -9 = (1, F (scaleFloat 6 x), F (scaleFloat 11 x))
                     | otherwise = (2, F (scaleFloat 9 x), F (scaleFloat 14 x))

scaleFloatTest2 :: NaNEq -> NaNEq
scaleFloatTest2 (F x) | -1.93e-43 <= x, x <= -1.92e-43 = F (scaleFloat 9 x)
                      | otherwise = F 0
