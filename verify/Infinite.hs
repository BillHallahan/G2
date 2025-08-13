{-# LANGUAGE BangPatterns #-}

module Zeno where

import Prelude
  ( Eq
  , Ord
  , Show
  , iterate
  , (!!)
  , fmap
  , Bool(..)
  , div
  , return
  , (.)
  , (||)
  , (==)
  , ($)
  )

-- code here adapted from HipSpec.hs

infix 1 =:=

infixr 0 ==>

-- simplification to remove Prop type

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

givenBool :: Bool -> Bool -> Bool
givenBool = given

(==>) :: Bool -> Bool -> Bool
(==>) = given

proveBool :: Bool -> Bool
proveBool lhs = lhs =:= True

(=:=) :: Eq a => a -> a -> Bool
(=:=) = (==)

-- everything here mainly copied from HipSpec, with some simplifications

data Nat = S Nat | Z
  deriving (Eq,Show,Ord)

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq,Ord,Show)

-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers

Z     === Z     = True
Z     === _     = False
(S _) === Z     = False
(S x) === (S y) = x === y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y
max x     Z     = x
max (S x) (S y) = S (max x y)

-- List functions

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n === x of
    True -> delete n xs
    False -> x : (delete n xs)

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n === x of
    True -> True
    False -> elem n xs

drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x === y of
    True -> S (count x ys)
    _ -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n === x of
    True -> x : xs
    _ -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

butlastConcat :: [a] -> [a] -> [a]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

--  New functions for infinite values
infNat :: Nat
infNat = S infNat

repeat :: a -> [a]
repeat x = x:repeat x

cycle :: [a] -> [a]
cycle xs = xs ++ cycle xs

-- Properties

prop_01 :: Nat -> Bool
prop_01 x = x <= infNat

prop_02 :: Nat -> Bool
prop_02 x = x <= (x + infNat)

prop_03 :: Nat -> Bool
prop_03 x = min x infNat =:= x

prop_04 :: [a] -> Bool
prop_04 xs = len (zip xs (repeat Z)) =:= len xs 

-- Inspired by Zeno.hs prop_03
prop_05 :: Nat -> [Nat] -> [Nat] -> Bool
prop_05 n xs ys = proveBool (count n xs <= count n (cycle xs ++ ys))

-- Inspired by Zeno.hs prop_06
prop_06 :: Nat -> Nat -> Bool
prop_06 n m = (n - (n + infNat) =:= Z)

-- Inspired by Zeno.hs prop_26
prop_07 :: Nat -> [Nat] -> [Nat] -> Bool
prop_07 x xs ys
  = givenBool (x `elem` xs)
  ( proveBool (x `elem` (cycle (xs ++ ys))) )

-- Inspired by Zeno.hs prop_26
prop_08 :: Nat -> [Nat] -> [Nat] -> Bool
prop_08 x xs ys
  = givenBool (x `elem` (cycle xs))
  ( proveBool (x `elem` (xs ++ ys)) )

-- Inspired by Zeno.hs prop_27
prop_09 :: Nat -> [Nat] -> [Nat] -> Bool
prop_09 x xs ys
  = givenBool (x `elem` ys)
  ( proveBool (x `elem` (cycle (xs ++ ys))) )

-- Inspired by Zeno.hs prop_27
prop_10 :: Nat -> [Nat] -> [Nat] -> Bool
prop_10 x xs ys
  = givenBool (x `elem` (cycle ys))
  ( proveBool (x `elem` (xs ++ ys)) )

-- Inspired by Zeno.hs prop_29
prop_11 :: Nat -> [Nat] -> Bool
prop_11 x xs
  = proveBool (x `elem` ins1 x (cycle xs))

-- Inspired by Zeno.hs prop_30
prop_12 :: Nat -> [Nat] -> Bool
prop_12 x xs
  = proveBool (x `elem` ins x (cycle xs))

-- Inspired by Zeno.hs prop_31
prop_13 :: Nat -> Nat -> Bool
prop_13 a b
  = (min (min a b) infNat =:= min a (min b infNat))

-- Inspired by Zeno.hs prop_32
prop_14 :: Nat -> Bool
prop_14 a
  = (min a infNat =:= min infNat a)

-- Inspired by Zeno.hs prop_33
prop_15 :: Nat -> Bool
prop_15 a
  = (min a infNat === a =:= a <= infNat)

-- Inspired by Zeno.hs prop_34
prop_16 :: Nat -> Bool
prop_16 b
  = (min infNat b === b =:= b <= infNat)

-- Inspired by Zeno.hs prop_40
prop_17 :: Eq a => a -> Bool
prop_17 x = take Z (repeat x) =:= []

-- Inspired by Zeno.hs prop_41
prop_18 :: Eq b => Nat -> (a -> b) -> a -> Bool
prop_18 n f xs = take n (map f (repeat xs)) =:= map f (take n (repeat xs))

-- Inspired by Zeno.hs prop_41
prop_19 :: Eq b => Nat -> (a -> b) -> [a] -> Bool
prop_19 n f xs = take n (map f (cycle xs)) =:= map f (take n (cycle xs))

-- Inspired by Zeno.hs prop_42
prop_20 :: Eq a => Nat -> a -> a -> Bool
prop_20 n x y = (take (S n) (x:repeat y) =:= x:(take n (repeat y)))

-- Inspired by Zeno.hs prop_42
prop_21 :: Eq a => Nat -> a -> [a] -> Bool
prop_21 n x ys = (take (S n) (x:cycle ys) =:= x:(take n (cycle ys)))

-- Inspired by Zeno.hs prop_44
prop_22 :: Eq a => a -> [a] -> [a] -> Bool
prop_22 x xs ys
  = (zip (x:xs) (cycle ys) =:= zipConcat x xs (cycle ys))

-- Inspired by Zeno.hs prop_44
prop_23 :: Eq a => a -> [a] -> [a] -> Bool
prop_23 x xs ys
  = (zip (x:cycle xs) ys =:= zipConcat x (cycle xs) ys)

-- Inspired by Zeno.hs prop_45
prop_24 :: Eq a => a -> a -> [a] -> [a] -> Bool
prop_24 x y xs ys
  = (zip (x:xs) (y:cycle ys) =:= (x, y) : zip xs (cycle ys))

-- Inspired by Zeno.hs prop_45
prop_25 :: Eq a => a -> a -> [a] -> [a] -> Bool
prop_25 x y xs ys
  = (zip (x:cycle xs) (y:ys) =:= (x, y) : zip (cycle xs) ys)

-- Inspired by Zeno.hs prop_46
prop_26 :: Eq a => [a] -> Bool
prop_26 xs
  = (zip ([] :: [Nat]) xs =:= [])

-- Inspired by Zeno.hs prop_57
prop_27 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_27 n m xs
  = (drop n (take m (cycle xs)) =:= take (m - n) (drop n (cycle xs)))

-- Inspired by Zeno.hs prop_57
prop_28 :: Nat -> Nat -> [Nat] -> Bool
prop_28 x y xs
  = given (x === y =:= False)
  ( (elem x (ins y (cycle xs)) =:= elem x (cycle xs)) )

-- Inspired by Zeno.hs prop_80
prop_29 :: Eq a => Nat -> [a] -> [a] -> Bool
prop_29 n xs ys
  = (take n (xs ++ (cycle ys)) =:= take n xs ++ take (n - len xs) (cycle ys))

-- Inspired by Zeno.hs prop_81
prop_30 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_30 n m xs {- ys -}
  = (take n (drop m (cycle xs)) =:= drop m (take (n + m) (cycle xs)))

-- Inspired by Zeno.hs prop_82
prop_31 :: Eq a => Nat -> [a] -> [a] -> Bool
prop_31 n xs ys
  = (take n (zip (cycle xs) ys) =:= zip (take n (cycle xs)) (take n ys))

-- Inspired by Zeno.hs prop_82
prop_32 :: Eq a => Nat -> [a] -> [a] -> Bool
prop_32 n xs ys
  = (take n (zip xs (cycle ys)) =:= zip (take n xs) (take n (cycle ys)))

-- Inspired by Zeno.hs prop_84
prop_33 :: Eq a => [a] -> [a] -> [a] -> Bool
prop_33 xs ys zs
  = (zip (cycle xs) (ys ++ zs) =:=
           zip (take (len ys) (cycle xs)) ys ++ zip (drop (len ys) (cycle xs)) zs)

-- Inspired by Zeno.hs prop_84
prop_34 :: Eq a => [a] -> [a] -> [a] -> Bool
prop_34 xs ys zs
  = (zip xs ((cycle ys) ++ zs) =:=
           zip (take (len (cycle ys)) xs) (cycle ys) ++ zip (drop (len (cycle ys)) xs) zs)

-- Inspired by Zeno.hs prop_84
prop_35 :: Eq a => [a] -> [a] -> [a] -> Bool
prop_35 xs ys zs
  = (zip xs (ys ++ (cycle zs)) =:=
           zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) (cycle zs))

prop_36 :: Nat -> [Nat] -> Nat -> Bool
prop_36 n ns k = k <= count n (cycle ns)

prop_37 :: Nat -> (a -> Bool) -> [a] -> Bool
prop_37 k p xs = k <= len (filter p (cycle xs))