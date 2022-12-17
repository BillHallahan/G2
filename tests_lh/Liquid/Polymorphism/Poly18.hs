module Poly18 where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

data C a = Emp | C a (C a)

{-@ measure size :: C a -> Int
    size Emp = 0
    size (C x xs) = 1
  @-}

{-@ f :: { c:C a | size c == 0 } @-}
f :: C a
f = emp

emp :: C a
emp = Emp