module FoldlUsesPoly where

import Prelude hiding (length, foldl, max, min)

data CList a = Cons a (CList a) | Nil

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
sumMinAndMax xs = min xs + max xs

minInt :: CList Int -> Int
minInt = min

min :: Ord a => CList a -> a
min (Cons x xs) = min' x xs
min _ = error "Invalid index"

min' :: Ord a => a -> CList a -> a
min' x (Cons y xs) = if x < y then min' x xs else min' y xs
min' x _ = x

max :: Ord a => CList a -> a
max (Cons x xs) = max' x xs
max _ = error "Invalid index"

max' :: Ord a => a -> CList a -> a
max' x (Cons y xs) = if x > y then max' x xs else max' y xs
max' x _ = x

sum :: Num a => CList a -> a 
sum xs = foldl (+) 0 xs