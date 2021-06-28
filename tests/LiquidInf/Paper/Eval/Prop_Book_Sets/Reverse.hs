{-@ LIQUID "--no-termination" @-}

module Reverse (reverse) where

import Prelude hiding (reverse)
import Data.Set

{-@ type ListS a S = {v:[a] | listElts v = S} @-}
{-@ type ListEq a X = ListS a {listElts X}    @-}

{-@ reverse :: xs:[Int] -> ListEq Int xs @-}
reverse :: [Int] -> [Int]
reverse xs = revHelper [] xs

revHelper :: [Int] -> [Int] -> [Int]
revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs