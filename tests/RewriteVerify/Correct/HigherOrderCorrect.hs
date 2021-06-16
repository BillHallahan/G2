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
intMap _ [] = []
intMap f (h:t) = (f h) : (intMap f t)

intIterate :: (Int -> Int) -> Int -> [Int]
intIterate f n = n : (intIterate f (f n))

-- TODO
intFilter :: (Int -> Bool) -> [Int] -> [Int]
intFilter _ [] = []
intFilter f (h:t) = if f h then h:(intFilter f t) else intFilter f t

nonneg :: Int -> Bool
nonneg x = x >= 0

p1 :: Int -> Int
p1 x = x + 1

{-# RULES
"doubleMap" forall f g l . intMap f (intMap g l) = intMap (compose f g) l
"mapIterate" forall f  n . intMap f (intIterate f n) = intIterate f (f n)
"mapTake" forall f n l . intMap f (intTake n l) = intTake n (intMap f l)
"mapFilter" forall f g l . intMap g (intFilter (f . g) l) = intFilter f (intMap g l)
"mf" forall l . intMap p1 (intFilter (nonneg . p1) l) = intFilter nonneg (intMap p1 l)
  #-}