{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-termination" @-}

module FilterConcat2 (size) where

import Prelude hiding (concat)

data List = Int :+: List
          | Nil

{-@ measure size @-}
size :: List -> Int
size Nil = 0
size (x :+: xs) = 1 + size xs

{-@ concatFilterEven :: xs:List -> { ys:List | size ys <= size xs } @-}
concatFilterEven :: List -> List
concatFilterEven = filterEven

filterEven :: List -> List
filterEven (x :+: xs)
    | x `mod` 2 == 0 = x :+: filterEven xs
filterEven _ = Nil
