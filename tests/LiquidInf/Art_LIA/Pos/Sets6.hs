{-@ LIQUID "--no-termination" @-}
module Sets6 (test1) where

import Prelude hiding (elem)
import Data.Set

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

elem :: Int -> [Int] -> Bool
elem _ []     = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1      = elem 2 [2]