{-@ LIQUID "--no-termination" @-}

module InsertSortElems (insertSort) where

import qualified Data.Set as S

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

{-@ insert :: Int -> xs:[Int] -> {VV : [Int] | (Set_cup (listElts xs) (Set_sng 0) == listElts VV)} @-}
insert :: Int -> [Int] -> [Int]
insert x []     = [x]
insert x (y:ys) = y : insert x ys

{-@ insertSort :: xs:[Int] -> ListEq Int xs @-}
insertSort :: [Int] -> [Int]
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)