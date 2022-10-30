module Poly12 where

import Prelude hiding (length, map)

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ length :: xs:List a -> { s:Int | size xs == s } @-}
length :: List a -> Int
length Emp = 0
length (x :+: xs) = 1 + length xs

{-@ map :: (a -> b) -> xs:(List a) -> {ys : (List b) | size ys >= size xs } @-}
map   :: (a -> b) -> List a -> List b
map _ Emp = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop :: List Int -> {v:Bool | v} @-}
prop :: List Int -> Bool
prop xs = length xs == length (map id xs)
