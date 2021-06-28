module InsertSortElems (insertSort) where

import qualified Data.Set as S

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

insert :: Int -> [Int] -> [Int]
insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys

{-@ insertSort :: xs:[Int] -> ListEq Int xs @-}
insertSort :: [Int] -> [Int]
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)