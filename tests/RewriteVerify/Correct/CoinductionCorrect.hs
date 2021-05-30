module CoinductionCorrect where

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

{-# RULES
"forceIdempotent" forall l . intForce (intForce l) = intForce l
"dropNoRecursion" forall l . intDrop 0 l = l
"takeIdempotent" forall n l . intTake n (intTake n l) = intTake n l
  #-}