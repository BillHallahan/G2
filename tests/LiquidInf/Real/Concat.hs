{-@ LIQUID "--prune-unsorted" @-}

-- {-@ include <include/Concat.hquals> @-}

module Concat (size, sumsize) where

import Prelude hiding (concat)

data List a = a :+: List a
            | Emp

{-@ measure size @-}
size :: List a -> Int
size Emp = 0
size (x :+: xs) = 1 + size xs

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ measure sumsize @-}
sumsize :: List (List a) -> Int
sumsize Emp = 0
sumsize (x :+: xs) = size x + sumsize xs

{-@ concat :: x:List (List a) -> {v:List a | size v == sumsize x } @-}
concat :: List (List a) -> List a
concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys