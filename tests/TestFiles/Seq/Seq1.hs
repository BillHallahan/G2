module Seq1 where

import Data.List

-- Validation
floatEq :: (Eq a, RealFloat a) => a -> a -> Bool
floatEq x y | isNaN x, isNaN y = True
            | isInfinite x, isInfinite y = True
            | otherwise = x == y

floatListEq :: (Eq a, RealFloat a) => [a] -> [a] -> Bool
floatListEq [] [] = True
floatListEq (x:xs) (y:ys) = floatEq x y && xs `floatListEq` ys
floatListEq _ _ = False

newtype NIE a = NIE [a]

instance (Eq a, RealFloat a) => Eq (NIE a) where
    NIE x == NIE y = floatListEq x y

nieWrapSnd :: (a, [b]) -> (a, NIE b)
nieWrapSnd (x, y) = (x, NIE y)

-- Tests

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


appendEqInt :: [Int] -> [Int]
appendEqInt s = s ++ [1]

-- ...

con2 :: Num a => [a] -> [a] -> (Int, [a])
con2 xs ys = case xs ++ ys of
    xs@(_:_:_) -> (3, xs)
    xs@(_:_) -> (2, xs)
    [] -> (1, [])

con2Int :: [Int] -> [Int] -> (Int, [Int])
con2Int = con2
con2Integer :: [Integer] -> [Integer] -> (Int, [Integer])
con2Integer = con2
con2Float :: [Float] -> [Float] -> (Int, NIE Float)
con2Float x y = nieWrapSnd (con2 x y)
con2Double :: [Double] -> [Double] -> (Int, NIE Double)
con2Double x y = nieWrapSnd (con2 x y)

con3 :: (Eq a, Num a) => [a] -> (Int, [a])
con3 xs
    | [] <- xs = (0, xs)
    | (y:ys) <- xs
    , 1:ys ++ ys == xs = (1, ys)
    | otherwise = (2, xs)

con3Int :: [Int] -> (Int, [Int])
con3Int = con3
con3Integer :: [Integer] -> (Int, [Integer])
con3Integer = con3
con3Float :: [Float] -> (Int, NIE Float)
con3Float = nieWrapSnd . con3
con3Double :: [Double] -> (Int, NIE Double)
con3Double = nieWrapSnd . con3
