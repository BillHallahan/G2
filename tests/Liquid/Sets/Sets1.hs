module Sets1 where

import Data.Set

{-@ type True  = {v:Bool |     v} @-}

{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y = (x `intersection` y) == x

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = (x `union` (y `union` z)) == x `union` z