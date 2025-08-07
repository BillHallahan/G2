module NatList1 where

import Prelude
  ( Eq
  , Ord
  , Show
  , iterate
  , (!!)
  , fmap
  , Bool(..)
  , div
  , return
  , (.)
  , (||)
  , (==)
  , ($)
  )

data Nat = S Nat | Z
  deriving (Show,Ord)

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

con :: Nat -> a -> b -> b
con n x y = if n == Z then con n x y else y

g :: Nat -> Nat
g x = g x

prop1False = con (S Z) (g Z) False