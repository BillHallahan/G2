module CoinductionIncorrect where

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

{-# RULES
"forceDoesNothing" forall l . intForce l = l
"badDropSum" forall n m l . intDrop n $ intDrop m l = intDrop (n + m) l
"doubleTake" forall n m l . intTake n (intTake m l) = intTake n l
"badDoubleReverse" forall l . intReverse (intReverse l) = l
  #-}