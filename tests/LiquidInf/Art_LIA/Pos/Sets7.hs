module Sets7 (test1, dElt) where

import Prelude hiding (elem)
import Data.Set

{-@ type True  = {v:Bool |     v} @-}

data D = D Int

{-@ measure dElt @-}
dElt (D x) = singleton x

{-@ elem      :: Int -> D -> Bool @-}
elem :: Int -> D -> Bool
elem x (D y) = x == y

{-@ test1 :: True @-}
test1      = elem 2 (D 2)