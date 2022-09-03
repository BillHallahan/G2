module FoldlUses where

import Prelude hiding (length, foldl)

data CList = Cons Int CList | Nil

getNth :: CList -> Int -> Int 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = error "Invalid index"

length :: CList -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

range :: Int -> Int -> CList 
range i j 
  | i < j     = Cons i (range (i+1) j)
  | otherwise = Nil 

foldl :: (Int -> Int -> Int) -> Int -> CList -> Int 
foldl f acc Nil         = acc 
foldl f acc (Cons x xs) = foldl f (f acc x) xs 

sum_foldl :: CList -> Int 
sum_foldl xs        = foldl add 0 is 
  where 
    add acc i = acc + getNth xs i
    is        = range 0 (length xs)

dotProd :: CList -> CList -> Int 
dotProd xs ys = foldl add 0 is 
  where 
    add acc i = acc + (getNth xs i * getNth ys i) 
    is        = range 0 (length xs) 
