module List7 where

import Prelude
  ( Eq
  , Ord
  , Show
  , Int
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

map :: (Int -> Int) -> [Int] -> [Int]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

drop :: Nat -> [Int] -> [Int]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

p1False :: (Int -> Int) -> [Int] -> Bool
p1False f xs = (map f xs == map f (drop Z xs))
