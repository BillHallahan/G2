{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module IsaplannerFalse where

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
  , min
  , max
  , (+)
  , (<=)
  , (<)
  , (>=)
  , (>)
  , (-)
  , Int
  , fst
  , snd
  , otherwise
  )

import Isaplanner

import G2.Plugin
import G2.Plugin.Prim
import G2.Plugin.Unsafe

{-# ANN module ("--smt-tuples --higher-order uninterpreted")
    #-}

{-# ANN prop_13_false Prop #-}
prop_13_false :: Nat -> Nat -> [Nat] -> Bool
prop_13_false n x xs
  = (drop (1 + n) (x : xs) =:= drop n xs)

{-# ANN prop_19_false Prop #-}
prop_19_false :: Nat -> [Nat] -> Bool
prop_19_false n xs
  = (len (drop n xs) =:= len xs - n)

{-# ANN prop_42_false Prop #-}
prop_42_false :: Nat -> Nat -> [Nat] -> Bool
prop_42_false n x xs
  = (take n (x:xs) =:= x : (take (n - 1) xs))

{-# ANN prop_56_false Prop #-}
prop_56_false :: Nat -> Nat -> [Nat] -> Bool
prop_56_false n m xs
  = (drop n (drop m xs) =:= drop (n + m) xs)

{-# ANN prop_57_false Prop #-}
prop_57_false :: Nat -> Nat -> [Nat] -> Bool
prop_57_false n m xs
  = (drop n (take m xs) =:= take (m - n) (drop n xs))

{-# ANN prop_67_false Prop #-}
prop_67_false :: [Nat] -> Bool
prop_67_false xs
  = (len (butlast xs) =:= len xs - 1)

{-# ANN prop_81_false Prop #-}
prop_81_false :: Nat -> Nat -> [Nat] -> Bool
prop_81_false n m xs {- ys -}
  = (take n (drop m xs) =:= drop m (take (n + m) xs))
