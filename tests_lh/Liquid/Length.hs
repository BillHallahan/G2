{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module List ( List, size ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

data List = Emp
          | (:+:) Int List
          deriving (Eq, Ord, Show)

{-@ measure size @-}
size :: List -> Int
size (Emp)        = 0
size ((:+:) x xs) = 1 + size xs

{-@ invariant {v:List | 0 <= size v} @-}

{-@ prop_size :: TRUE @-}
prop_size  = size l0 == 0

{-@ l0 :: List @-}
l0 = Emp