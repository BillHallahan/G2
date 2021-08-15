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

-- TODO more diagnosis attempts

listConcat :: [[a]] -> [a]
listConcat [] = []
listConcat (h:t) = h ++ (listConcat t)

listLength :: [a] -> Int
listLength [] = 0
listLength (_:t) = 1 + listLength t

lmap :: (a -> b) -> [a] -> [b]
lmap _ [] = []
lmap f (h:t) = (f h) : (lmap f t)

expLength :: [a] -> Int
expLength [] = 0
expLength (_:t) = 1 + expLength t + expLength t

doubleLength :: [a] -> Int
doubleLength [] = 1
doubleLength (_:t) = doubleLength t + doubleLength t

-- TODO forceConcat is actually invalid
{-# RULES
"mapLength" forall f l . listLength (intMap f l) = listLength l
"forceLength" forall l . listLength (intForce l) = listLength l
"forceConcat" forall m . listConcat (lmap intForce m) = intForce (listConcat m)
"exp" forall x xs . expLength (x:xs) = 1 + (2 * expLength xs)
"double" forall x xs . doubleLength (x:xs) = 2 * doubleLength xs
  #-}

-- TODO Nats instead of Ints
data Nat = Z
         | S Nat

addNat :: Nat -> Nat -> Nat
addNat Z y = y
addNat (S x) y = S (addNat x y)

doubleNat :: Nat -> Nat
doubleNat Z = Z
doubleNat (S x) = S (S (doubleNat x))

expLengthNat :: [a] -> Nat
expLengthNat [] = Z
expLengthNat (_:t) = S (addNat (expLengthNat t) (expLengthNat t))

idInt :: Int -> Int
idInt x = x

len :: [a] -> Int
len [] = 0
len (_:t) = 1 + len t

lenDouble :: [a] -> Int
lenDouble [] = 0
lenDouble (_:t) = 1 + (lenDouble t) + 1

zeroList :: [a] -> Int
zeroList [] = 0
zeroList (_:t) = 0 + (zeroList t) + 0

pz :: Int -> Int
pz x = 0 + x + 0

-- TODO expReduced runs forever too
-- TODO listMinus terminates, but lenDouble does not
-- ld runs forever, but UNSAT for lpm
-- UNSAT for zl1, runs forever on zl2
-- UNSAT for branch2, runs forever for branch3
-- UNSAT for branch4, branch5, branch6
{-# RULES
"expNat" forall x xs . expLengthNat (x:xs) = S (doubleNat (expLengthNat xs))
"expReduced" forall xs . expLength xs = (2 * expLength xs) - (expLength xs)
"doubleMinus" forall x . idInt x = (2 * x) - x
"listMinus" forall xs . len xs = (2 * (len xs)) - (len xs)
"lenDouble" forall xs . lenDouble xs = (2 * (lenDouble xs)) - (lenDouble xs)
"ld" forall xs . lenDouble xs = 1 + (lenDouble xs) - 1
"lpm" forall xs . len xs = 1 + (len xs) - 1
"zl" forall xs . zeroList xs = 0 + (zeroList xs) + 0
"zl1" forall x xs . zeroList (x:xs) = zeroList xs
"zl2" forall xs . pz (zeroList xs) = zeroList xs
"zz" forall xs . zeroList xs = zeroList xs
"branch2" forall xs . zeroList xs = (zeroList xs) + (zeroList xs)
"branch3" forall xs . zeroList xs = (zeroList xs) + (zeroList xs) + (zeroList xs)
"zeroAdd" pz 0 = pz (0 + 0 + 0 + 0 + 0)
"b3" forall xs . zeroList xs = 0 + 0 + 0
"branch4" forall xs . zeroList xs = (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs)
"branch5" forall xs . zeroList xs = (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs)
"branch6" forall xs . zeroList xs = (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs) + (zeroList xs)
  #-}
