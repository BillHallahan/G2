{-# LANGUAGE BangPatterns #-}

module CoinductionIncorrect where

import Data.List

cons :: t -> [t] -> [t]
cons n (!l) = n:l

intForce :: [Int] -> [Int]
intForce [] = []
intForce (h:t) = cons h $ intForce t

maybeForce :: Maybe t -> Maybe t
maybeForce !Nothing = Nothing
maybeForce !(Just !x) = Just x

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

-- TODO new example
con :: Int -> Int
con x = x

f :: Int -> Int
f x = x + 1

g :: Int -> Int
g x = x + 2

{-# RULES
"doubleMapBackward" forall l . intMap p1 (intMap t2 l) = intMap (t2 . p1) l
"badMapIterate" forall n . intMap p1 (intIterate p1 n) = intIterate p1 n
"badMapTake" forall n l . intMap p1 (intTake n l) = intTake n (intMap t2 l)
"badCon" forall x . con (f x) = con (g x)
  #-}

-- some of these rules are incorrect only because of laziness
{-# RULES
"badMaybeForce" forall (m :: Maybe Int) . maybeForce m = m
"forceDoesNothing" forall l . intForce l = l
"badDropSum" forall n m l . intDrop n (intDrop m l) = intDrop (n + m) l
"doubleTake" forall n m l . intTake n (intTake m l) = intTake n l
"badDoubleReverse" forall l . intReverse (intReverse l) = l
"takeDropCancel" forall n l . intDrop n (intTake n l) = []
  #-}
