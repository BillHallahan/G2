{-@ LIQUID "--prune-unsorted" @-}

-- {-@ include <include/Concat2.hquals> @-}

module Concat2 (size, sumsize) where

import Prelude hiding (concat)

data List a = a :+: List a
			| Nil

{-@ measure size @-}
size :: List a -> Int
size Nil = 0
size (x :+: xs) = 1 + size xs

{-@ measure sumsize @-}
sumsize :: List (List a) -> Int
sumsize Nil = 0
sumsize (x :+: xs) = size x + sumsize xs

{-@ concat :: x:List (List a) -> {v:List a | size v == sumsize x } @-}
concat :: List (List a) -> List a
concat Nil = Nil
concat (xs :+: Nil) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

append :: List a -> List a -> List a
append xs Nil = xs
append Nil ys = ys
append (x :+: xs) ys = x :+: append xs ys