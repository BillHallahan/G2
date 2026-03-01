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
  deriving Show

map :: (Int -> Int) -> [Int] -> [Int]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

drop :: Nat -> [Int] -> [Int]
drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

p1 :: (Int -> Int) -> [Int] -> Bool
p1 f xs = (map f xs == map f (drop Z xs))
