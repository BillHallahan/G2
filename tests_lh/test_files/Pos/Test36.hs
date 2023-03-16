
module Test36 (f) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

data C a = Emp | C a (C a)

{-@ measure size :: C a -> Int
        size Emp = 0
        size (C x xs) = 1 + size xs
  @-}

emp :: C a
emp = Emp

{-@ f :: a -> { c:C a | size c == 1 } @-}
f :: a -> C a
f x = C x emp