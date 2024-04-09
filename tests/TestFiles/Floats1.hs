{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Floats1 where

newtype NaNEq = F { unF :: Float } deriving (Ord, Num, Fractional, Floating, Real, RealFrac, RealFloat)

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
f :: Float -> Float
f x | abs(x - 9.1) < 0.001  = x + 0.1
    | otherwise = x

fConc :: Float
fConc = f 9.1

{-# NOINLINE g #-}
g :: Float -> Float
g x = 2 * f x

gConc :: Float
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
