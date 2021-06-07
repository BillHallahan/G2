module CoinductionCorrect where

import Data.List

-- TODO make sure this is correct
intForce :: [Int] -> [Int]
intForce [] = []
intForce (h:t) =
  case intForce t of
    t' -> h:t'

-- also have a rule about a non-strict function
-- TODO runs forever on negatives, has error case
-- TODO adjust the error cases?
intDrop :: Int -> [Int] -> [Int]
intDrop 0 l = l
intDrop n (_:t) =
  if n < 0
  then error "negative input"
  else intDrop (n - 1) t
intDrop _ [] = error "list not long enough"

-- TODO strictness might be an issue here
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
intMap = Data.List.map

intIterate :: (Int -> Int) -> Int -> [Int]
intIterate f n = n : (intIterate f (f n))

p1 :: Int -> Int
p1 = (+ 1)

t2 :: Int -> Int
t2 = (* 2)

{-# RULES
"doubleMap" forall l . intMap p1 (intMap t2 l) = intMap (p1 . t2) l
"mapIterate" forall n . intMap p1 (intIterate p1 n) = intIterate p1 (n + 1)
"mapTake" forall n l . intMap p1 (intTake n l) = intTake n (intMap p1 l)
  #-}

{-# RULES
"forceIdempotent" forall l . intForce (intForce l) = intForce l
"dropNoRecursion" forall l . intDrop 0 l = l
"takeIdempotent" forall n l . intTake n (intTake n l) = intTake n l
"doubleReverse" forall l . intReverse (intReverse l) = intForce l
  #-}