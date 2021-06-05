{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-termination" @-}

-- {-@ include <include/Concat2.hquals> @-}

module FilterConcat (size) where

import Prelude hiding (concat)

data List a = a :+: List a
            | Nil

{-@ measure size @-}
size :: List a -> Int
size Nil = 0
size (x :+: xs) = 1

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ f :: xs:List Int -> { ys:List Int | size ys <= 0 } @-}
f :: List Int -> List Int
f xs = g xs

{-@ g :: xs:List Int -> List Int @-}
g :: List Int -> List Int
g _ = Nil