module Sets9 (f) where

import qualified Data.Set as S

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

{-@ f :: xs:[Int] -> ListEq Int xs @-}
f :: [Int] -> [Int]
f []     = []
f (x:xs) = g x (f xs)

{-@ g :: Int -> [Int] -> {xs : [Int] | (Set_mem 0 (listElts xs))} @-}
g :: Int -> [Int] -> [Int]
g x [] = [x]
g x ys = x:ys

