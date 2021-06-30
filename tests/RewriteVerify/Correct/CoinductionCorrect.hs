{-# LANGUAGE BangPatterns #-}

module CoinductionCorrect where

import Data.List

cons :: t -> [t] -> [t]
cons n (!l) = n:l

intForce :: [Int] -> [Int]
intForce [] = []
intForce (h:t) = cons h $ intForce t

intDrop :: Int -> [Int] -> [Int]
intDrop 0 l = l
intDrop n (_:t) =
  if n < 0
  then error "negative input"
  else intDrop (n - 1) t
intDrop _ [] = error "list not long enough"

intTake :: Int -> [Int] -> [Int]
intTake 0 _ = []
intTake n (h:t) =
  if n < 0
  then error "negative input"
  else h:(intTake (n - 1) t)
intTake _ [] = error "list not long enough"

intReverse :: [Int] -> [Int]
intReverse [] = []
intReverse (h:t) = (intReverse t) ++ [h]

intMap :: (Int -> Int) -> [Int] -> [Int]
intMap _ [] = []
intMap f (h:t) = (f h) : (intMap f t)

intIterate :: (Int -> Int) -> Int -> [Int]
intIterate f n = n : (intIterate f (f n))

p1 :: Int -> Int
p1 = (+ 1)

t2 :: Int -> Int
t2 = (* 2)

nonterm1 :: Bool -> Bool
nonterm1 b = nonterm2 b

nonterm2 :: Bool -> Bool
nonterm2 b = nonterm3 b

nonterm3 :: Bool -> Bool
nonterm3 b = nonterm1 b

{-# RULES
"doubleMap" forall l . intMap p1 (intMap t2 l) = intMap (p1 . t2) l
"mapIterate" forall n . intMap p1 (intIterate p1 n) = intIterate p1 (p1 n)
"mapTake" forall n l . intMap p1 (intTake n l) = intTake n (intMap p1 l)
  #-}

{-# RULES
"forceIdempotent" forall l . intForce (intForce l) = intForce l
"dropNoRecursion" forall l . intDrop 0 l = l
"takeIdempotent" forall n l . intTake n (intTake n l) = intTake n l
"doubleReverse" forall l . intReverse (intReverse l) = intForce l
  #-}

{-# RULES
"corecursion" forall b . nonterm1 b = nonterm2 b
"nontermNegation" forall b . nonterm1 b = not (nonterm1 b)
  #-}
