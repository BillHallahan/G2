{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-termination" @-}

-- {-@ include <include/Concat2.hquals> @-}

module FilterConcat (size, sumsize) where

import Prelude hiding (concat)

data List a = a :+: List a
            | Nil

{-@ measure size @-}
size :: List a -> Int
size Nil = 0
size (x :+: xs) = 1 + size xs

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ measure sumsize @-}
sumsize :: List (List a) -> Int
sumsize Nil = 0
sumsize (x :+: xs) = size x + sumsize xs

{-@ concatFilterEven :: xs:List (List Int) -> { ys:List Int | size ys <= sumsize xs } @-}
concatFilterEven :: List (List Int) -> List Int
concatFilterEven xs = filterEven (concat xs)

{-@ filterEven :: xs:List Int -> List Int @-}
filterEven :: List Int -> List Int
filterEven Nil = Nil
filterEven (x :+: xs)
    | x `mod` 2 == 0 = x :+: filterEven xs
    | otherwise = filterEven xs

{-@ concat :: List (List a) -> List a @-}
concat :: List (List a) -> List a
concat Nil = Nil
concat (xs :+: Nil) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

{-@ append :: List a -> List a -> List a @-}
append :: List a -> List a -> List a
append xs Nil = xs
append Nil ys = ys
append (x :+: xs) ys = x :+: append xs ys