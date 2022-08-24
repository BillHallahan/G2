{-@ LIQUID "--no-termination" @-}

module MergeSortElems (f) where

import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}

{-@ f :: xs:[Int] -> ListEq Int xs @-}
f :: [Int] -> [Int]
f []  = []
f xs  = append ys zs
  where
   (ys, zs)   = g xs

-- {-@ g   :: xs:[a] -> {t:([a], [a]) | Set_cup (listElts (fst t)) (listElts (snd t)) == listElts xs} @-}
g            :: [Int] -> ([Int], [Int])
g (x:zs) = ([x], zs)
g xs       = ([], xs)

-- {-@ append :: xs:[a] -> ys:[a] -> { zs:[a] | Set_cup (listElts xs) (listElts ys) == listElts zs } @-}
append :: [Int] -> [Int] -> [Int]
append []     ys = ys
append (x:xs) ys = x : append xs ys