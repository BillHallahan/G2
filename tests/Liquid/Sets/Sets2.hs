module Sets1 where

import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}

{-@ type ListUn a X Y = ListS a {Set_cup (listElts X) (listElts Y)} @-}

{-@ badIdList :: xs:[a] -> { ys:[a] | listElts xs == listElts ys } @-}
badIdList :: [a] -> [a]
badIdList xs = []

{-@ append       :: xs:[a] -> ys:[a] -> ListUn a xs ys @-}
append :: [a] -> [a] -> [a]
append []     ys = []
append (x:xs) ys = x : append xs ys