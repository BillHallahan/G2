module InsertSortElems (insertSort) where

import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys

{-@ insertSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)