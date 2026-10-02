-- Property from "Productive Use of Failure in Inductive Proof",
-- Andrew Ireland and Alan Bundy, JAR 1996
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module ProdFalse where

import Prelude(Bool(..), Int, (+), (*), (-), (>), (/=), (==), (<=), even, div, Eq, id, error)

import Prelude ((>=), mod)

import Prod

import G2.Plugin hiding ((==>))
import G2.Plugin.Unsafe
import G2.Plugin.Prim

{-# ANN module ("--smt-tuples --higher-order uninterpreted")
    #-}

{-# ANN prop_L04_false Prop #-}
prop_L04_false :: Eq a => Nat -> Nat -> a -> [a] -> Bool
prop_L04_false w x y zs =
  drop (w + 1) (drop x (y:zs)) === drop w (drop x zs)

{-# ANN prop_L05_false Prop #-}
prop_L05_false :: Eq a => Nat -> Nat -> a -> a -> [a] -> Bool
prop_L05_false v w x y zs =
  drop (v + 1) (drop (w + 1) (x : (y : zs))) === drop (v + 1) (drop w (x : zs))

{-# ANN prop_L06_false Prop #-}
prop_L06_false :: Eq a => Nat -> Nat -> Nat -> a -> [a] -> Bool
prop_L06_false v w x y z =
  drop (v + 1) (drop w (drop x (y:z))) === drop v (drop w (drop x z))

{-# ANN prop_L07_false Prop #-}
prop_L07_false :: Eq a => Nat -> Nat -> Nat -> a -> a -> [a] -> Bool
prop_L07_false u v w x y z =
  drop (u + 1) (drop v (drop (w + 1) (x : (y : z)))) ===
  drop (u + 1) (drop v (drop w (x:z)))
