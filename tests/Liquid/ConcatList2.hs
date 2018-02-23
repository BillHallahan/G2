module ConcatList2 where

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

import Prelude hiding (concat)

--flycheck_List.lhs-2015-03-20T17.52.22.lhs

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}


{-@ measure sumsize      :: List (List a) -> Int
    sumsize (Emp)        = 0
    sumsize ((:+:) x xs) = size x + sumsize xs
  @-}

{-@ concat :: x:List (List a) -> {v:List a | size v = sumsize x} @-}
concat :: List (List a) -> List a
concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((concat' xs ys) :+: xss)

{-@ concat' :: List a -> List a -> List a @-}
concat' :: List a -> List a -> List a
concat' Emp Emp = Emp
concat' xs Emp = xs
concat' Emp ys = ys
concat' (x :+: xs) ys = x :+: concat' xs ys
