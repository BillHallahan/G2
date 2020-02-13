{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined () where

import qualified Data.Map as M

import Data.List (minimumBy, head)

data List a = Emp
            | R a
              deriving (Eq, Ord, Show)

{-@ measure size :: List a -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ f :: [{v:Int | v == 1 }] -> List {v:Int | v == 1 } @-}
f :: [Int] -> List Int
f cs = kvsm
  where
    kvs   = R (g cs)
    kvsm  = h kvs

{-@ g :: [{v:Int | v == 1 }] -> Int @-}
g :: [Int] -> Int
g xs = minimumBy (\_ _ -> EQ) xs

{-@ h :: List Int -> List Int @-}
h :: List Int -> List Int
h Emp = Emp
h (R _) = R 1