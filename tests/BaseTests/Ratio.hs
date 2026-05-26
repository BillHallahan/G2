module Ratio where

import Data.Ratio

manipRatio :: Int -> Int -> Ratio Int
manipRatio x1 y1
    | x > y = x + y
    | otherwise = x - y
    where
        x = x1 % 1
        y = y1 % 1

callApprox :: Int -> Int -> Rational
callApprox x y = approxRational (x % 1) (y % 1)