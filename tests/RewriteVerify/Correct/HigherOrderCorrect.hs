module CoinductionCorrect where

import Data.List

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
intMap p (h:t) = (p h) : (intMap p t)

intIterate :: (Int -> Int) -> Int -> [Int]
intIterate q n = n : (intIterate q (q n))

intFilter :: (Int -> Bool) -> [Int] -> [Int]
intFilter _ [] = []
intFilter r (h:t) = if r h then h:(intFilter r t) else intFilter r t

nonneg :: Int -> Bool
nonneg x = x >= 0

p1 :: Int -> Int
p1 x = x + 1

intMap1 :: (Int -> Int) -> [Int] -> [Int]
intMap1 _ [] = []
intMap1 f (h:t) = (f h) : (intMap2 f t)

intMap2 :: (Int -> Int) -> [Int] -> [Int]
intMap2 _ [] = []
intMap2 f (h:t) = (f h) : (intMap1 f t)

{-# RULES
"doubleMap" forall f g l . intMap f (intMap g l) = intMap (compose f g) l
"mapIterate" forall f  n . intMap f (intIterate f n) = intIterate f (f n)
"mapTake" forall f n l . intMap f (intTake n l) = intTake n (intMap f l)
"mapFilter" forall f g l . intMap g (intFilter (f . g) l) = intFilter f (intMap g l)
"mf" forall l . intMap p1 (intFilter (nonneg . p1) l) = intFilter nonneg (intMap p1 l)
  #-}

{-# RULES
"corecursiveMap" forall f l . intMap1 f l = intMap f l
  #-}
