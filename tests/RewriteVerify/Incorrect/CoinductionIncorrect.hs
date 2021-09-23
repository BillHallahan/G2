{-# LANGUAGE BangPatterns #-}

module CoinductionIncorrect where

import Data.List

cons :: t -> [t] -> [t]
cons n (!l) = n:l

intForce :: [a] -> [a]
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

con :: Int -> Int
con x = x

f :: Int -> Int
f x = x + 1

g :: Int -> Int
g x = x + 2

nonterm :: Bool -> Bool
nonterm b = nonterm b

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
"badBool" forall b . nonterm b = True
  #-}

-- With normal stopping rules, this gets stuck with "let w = w in w"
-- with the [] [] version, badNil gets UNSAT
-- being more generous with stopping points prevents it from getting stuck too
badZip :: [Int] -> [Int] -> [(Int, Int)]
badZip _ [] = let w = w in w -- badZip [] []
badZip [] _ = let w = w in w -- badZip [] []
badZip (x:xs) (y:ys) = (x, y):(badZip xs ys)

-- this gets UNSAT without any totality or finiteness restrictions
-- Is this correct behavior?  Yes, because they both fail to terminate
bad1 :: Int -> Int
bad1 x = bad1 x

bad2 :: Int -> Int
bad2 x = bad2 x

{-# RULES
"bz" forall xs ys . intForce (badZip xs ys) = badZip xs ys
"badPair" forall x . bad1 x = bad2 x
"badNil" intForce (badZip [] []) = badZip [] []
  #-}

-- TODO this is confirmation that the current version of induction is unsound
-- also want an easily-readable trace
-- new data type called Steps:  one constructor for each rule we apply
-- show the steps taken at the end
-- show the expression pairs used for matching
match1 :: [Int] -> Int
match1 [] = 1
match1 ([_]) = 2
match1 _ = 4

match2 :: [Int] -> Int
match2 [] = 1
match2 ([_]) = 2
match2 _ = 3

badlist :: [Int] -> [Int]
badlist xs = badlist xs

{-# RULES
"badlist" forall xs . match1 (intForce xs) = match2 (intForce xs)
  #-}
