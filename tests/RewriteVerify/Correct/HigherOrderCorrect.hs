module CoinductionCorrect where

import Data.List

-- TODO strictness might be an issue here
intTake :: Int -> [Int] -> [Int]
intTake 0 _ = []
intTake n (h:t) =
  if n < 0
  then error "negative input"
  else h:(intTake (n - 1) t)
intTake _ [] = error "list not long enough"

compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int 
compose f g x = f (g x)

intMap :: (Int -> Int) -> [Int] -> [Int]
--intMap = Data.List.map
intMap _ [] = []
intMap f (h:t) = (f h) : (intMap f t)

intIterate :: (Int -> Int) -> Int -> [Int]
intIterate f n = n : (intIterate f (f n))

{-# RULES
"doubleMap" forall f g l . intMap f (intMap g l) = intMap (compose f g) l
"mapIterate" forall f  n . intMap f (intIterate f n) = intIterate f (f n)
"mapTake" forall f n l . intMap f (intTake n l) = intTake n (intMap f l)
  #-}