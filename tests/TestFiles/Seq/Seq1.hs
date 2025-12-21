module Seq1 where

import Data.List

toEnum1 :: [Int]
toEnum1 = [toEnum 56089]

conInt :: [Int] -> [Int] -> [Int]
conInt xs ys = xs ++ ys

conInteger :: [Integer] -> [Integer] -> [Integer]
conInteger xs ys = xs ++ ys

conFloat :: [Float] -> [Float] -> [Float]
conFloat xs ys = xs ++ ys

conDouble :: [Double] -> [Double] -> [Double]
conDouble xs ys = xs ++ ys

floatListEq :: (Eq a, RealFloat a) => [a] -> [a] -> Bool
floatListEq [] [] = True
floatListEq (x:xs) (y:ys) = floatEq x y && xs `floatListEq` ys
floatListEq _ _ = False

floatEq :: (Eq a, RealFloat a) => a -> a -> Bool
floatEq x y | isNaN x, isNaN y = True
            | isInfinite x, isInfinite y = True
            | otherwise = x == y