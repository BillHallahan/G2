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

{-# NOINLINE drop #-}
drop [] = []
drop (_:xs) = xs

{-# NOINLINE map #-}
map :: (a -> a) -> [a] -> [a]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

prop1 f xs
  = (drop (map f xs) == map f (drop xs))
