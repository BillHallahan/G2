module FoldlUsesPoly where

import Prelude hiding (length, foldl, max, min)

data CList a = Nil | Cons a (CList a) deriving (Eq, Ord)

data Pair a b = Pair a b

getNth :: CList a -> Int -> a
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = error "Invalid index"

length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

foldl :: (a -> b -> a) -> a -> CList b -> a 
foldl f acc Nil         = acc 
foldl f acc (Cons x xs) = foldl f (f acc x) xs 

sumMinAndMaxInt :: CList Int -> Int
sumMinAndMaxInt = sumMinAndMax

sumMinAndMax :: (Num a, Ord a) => CList a -> a
sumMinAndMax xs = min2 xs + max2 xs

minInt :: CList Int -> Int
minInt = min2

maxInt :: CList Int -> Int
maxInt = max2

min2 :: Ord a => CList a -> a
min2 (Cons x xs) = min' x xs
min2 _ = error "Invalid index"

min' :: Ord a => a -> CList a -> a
min' x (Cons y xs) = if x < y then min' x xs else min' y xs
min' x _ = x

max2 :: Ord a => CList a -> a
max2 (Cons x xs) = max' x xs
max2 _ = error "Invalid index"

max' :: Ord a => a -> CList a -> a
max' x (Cons y xs) = if x > y then max' x xs else max' y xs
max' x _ = x

maxInt' :: Int -> CList Int -> Int
maxInt' x xs = max' x xs

sum :: Num a => CList a -> a
sum xs = foldl (+) 0 xs

maxesInt :: CList Int -> CList Int -> Pair Int Int
maxesInt = maxes

maxes :: (Ord a, Ord b) => CList a -> CList b -> Pair a b
maxes xs ys = Pair (max2 xs) (max2 ys)

maxesIntAssert :: CList Int -> CList Int -> Pair Int Int -> Bool
maxesIntAssert _ _ (Pair a b) = a == 0

class Switchable f where
    switch :: f a b -> f b a

instance Switchable Pair where
    switch (Pair x y) = Pair y x

{-# NOINLINE switchP #-}
switchP :: Switchable f => f a b -> f b a
switchP = switch

switchInt :: Pair Int Int -> Pair Int Int
switchInt = switchP

data Holds a = H a

class In f where
    getIn :: f a -> f a

instance In Holds where
    getIn (H x) = H x

{-# NOINLINE getInP #-}
getInP :: In f => f a -> f a
getInP = getIn

getInInt :: Holds Int -> Holds Int
getInInt = getInP

-- Test 1: maxesInt assume maxesIntInputs assert maxesIntAss -- works well, old solution cannot deliver any results WHEN no. of states is not specified
-- both work equally well for 500 states
maxesIntInputs :: CList Int -> CList Int -> Pair Int Int -> Bool
maxesIntInputs a b _ = (a == (Cons 2 (Cons 0 (Cons 1 (Cons 3 (Cons 2 Nil)))))) && (b == (Cons 0 (Cons 4 (Cons 1 (Cons 2 (Cons 3 Nil))))))

prop_maxesInt_wrong :: CList Int -> CList Int -> Pair Int Int -> Bool
prop_maxesInt_wrong _ _ (Pair a b) = a > b
