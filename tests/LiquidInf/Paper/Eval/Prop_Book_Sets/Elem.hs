{-@ LIQUID "--no-termination" @-}

module Elem (test1, test2) where

import Prelude hiding (elem)
import Data.Set

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ elem      :: Int -> [Int] -> Bool @-}
elem :: Int -> [Int] -> Bool
elem _ []     = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1      = elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2      = elem 2 [1, 3]