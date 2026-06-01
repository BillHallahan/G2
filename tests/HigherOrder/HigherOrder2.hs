
module HigherOrder2 where

import Data.Foldable

eContFrac :: [Integer]
eContFrac = aux 2 where aux n = 1:n:1:aux (n+2)

ratTrans :: (Integer -> Integer -> Integer) -> (Integer,Integer,Integer,Integer) -> [Integer] -> [Integer]
-- Output a digit if we can
ratTrans f (a,b,c,d) xs |
  f c q <= f a b && c + c > a
     = q:ratTrans f (c,d,a,b) xs
  where q = b `div` d
ratTrans f (a,b,c,d) (x:xs) = ratTrans f (b,a+x*b,c,c+x) xs

takeDigits :: (Integer -> Integer -> Integer) -> Int -> [Integer] -> [Integer]
takeDigits _ 0 _ = []
takeDigits f n (x:xs) = x:takeDigits f (n-1) (ratTrans f (10,0,0,1) xs)

main :: (Integer -> Integer -> Integer) -> Int -> [Integer]
main symFun digits = takeDigits symFun digits eContFrac

compHigher :: ([Int] -> Int) -> [Int] -> Bool
compHigher f xs =
    case f xs == f xs of
      True -> False
      False -> True
  
foldrCall :: (Int -> Int -> Int) -> [Int] -> Bool
foldrCall f (_:_:_:_:_:_:_) = True
foldrCall f xs = not (foldr f 0 xs == foldr' f 0 xs)