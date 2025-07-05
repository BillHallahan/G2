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

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

prop1 n xs = take n xs ++ drop n xs == xs

prop1False n xs = take n xs ++ drop n xs == (case xs of [x, y] -> [x, y, 3]; _ -> xs) 
