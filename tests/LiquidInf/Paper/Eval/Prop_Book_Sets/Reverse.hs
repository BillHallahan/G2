module Reverse (reverse) where

import Prelude hiding (reverse)
import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

{-@ reverse :: xs:[a] -> ListEq a xs @-}
reverse xs = revHelper [] xs

revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs