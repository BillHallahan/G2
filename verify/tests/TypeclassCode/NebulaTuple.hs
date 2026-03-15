{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

-- Used to compare Nebula to Nova- Nebula crashes when run directly with the Tuple Monoid typeclass instance
-- and on tuple app composition, but can work (not crash) on this file.

module TypeclassCode.NebulaTuple where

import Prelude (Bool (..))

data Tuple a b = Tuple a b

data Nat
  = Z
  | S Nat

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

data List a = a :> List a | Nil
infixl 4 :>

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr k z Nil     = z
foldr k z (y :> ys) = y `k` foldr k z ys


(<>) :: Tuple Nat Nat -> Tuple Nat Nat -> Tuple Nat Nat
Tuple x1 y1 <> Tuple x2 y2 = Tuple (x1 + x2) (y1 + y2)

mempty = Tuple Z Z

mconcat :: List (Tuple Nat Nat) -> Tuple Nat Nat
mconcat = foldr (<>) mempty

fmap f (Tuple x y) = Tuple x (f y)

id :: a -> a
id x = x

(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

pure x = Tuple Z x

(<*>) :: Tuple Nat (a -> b) -> Tuple Nat a -> Tuple Nat b
Tuple x1 f <*> Tuple x2 y = Tuple (x1 + x2) (f y)
