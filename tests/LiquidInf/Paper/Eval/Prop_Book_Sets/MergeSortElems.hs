{-@ LIQUID "--no-termination" @-}

module MergeSortElems (mergeSort) where

import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}

{-@ mergeSort :: xs:[Int] -> ListEq Int xs @-}
mergeSort :: [Int] -> [Int]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = halve mid xs
   mid        = length xs `div` 2

-- {-@ merge :: xs:[a] -> ys:[a] -> { r:[a] | Set_cup (listElts xs) (listElts ys) == listElts r } @-}
merge :: [Int] -> [Int] -> [Int]
merge [] ys          = ys
merge xs []          = xs
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys

-- {-@ halve            :: Int -> xs:[a] -> {t:([a], [a]) | Set_cup (listElts (fst t)) (listElts (snd t)) == listElts xs} @-}
halve            :: Int -> [Int] -> ([Int], [Int])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

-- {-@ append :: xs:[a] -> ys:[a] -> { zs:[a] | Set_cup (listElts xs) (listElts ys) == listElts zs } @-}
append :: [Int] -> [Int] -> [Int]
append []     ys = ys
append (x:xs) ys = x : append xs ys