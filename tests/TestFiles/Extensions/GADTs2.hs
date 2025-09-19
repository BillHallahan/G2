{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module GADTs2 where

import GHC.TypeLits 
import Data.Kind

-- This file aims to provide more test cases to ensure that GADT works with G2
-- When trying to verify GADT code, we always use the flag --inst-after, --validate
-- It's also recommended that not to try gadt invovle recursion since it's will get pretty complicated pretty quickly

data Peano = Succ Peano | Zero 

data Vec :: Peano -> Type -> Type where
    VNil  :: Vec Zero a
    VCons :: forall n a. a -> Vec n a -> Vec (Succ n) a

instance Eq a => Eq (Vec Zero a) where
    VNil == VNil = True

instance (Eq a, Eq (Vec n a)) => Eq (Vec (Succ n) a) where
    (VCons x xs) == (VCons y ys) = x == y && xs == ys

-- Non-recursive GADTs
data Value a where 
    VInt :: Int -> Value Int 
    VBool :: Bool -> Value Bool

instance Eq (Value a) where
  VInt x  == VInt y  = x == y
  VBool x == VBool y = x == y

-- Convert a Value to a String
showValue :: Value a -> String
showValue (VInt n)  = show n
showValue (VBool b) = show b

-- Negate a Value Bool
notValue :: Value Bool -> Value Bool
notValue (VBool b) = VBool (not b)

-- Increment a Value Int
incValue :: Value Int -> Value Int
incValue (VInt n) = VInt (n + 1)

-- Existential GADTs
data SomeVec a where
  SomeVec :: Vec n a -> SomeVec a

instance Eq a => Eq (SomeVec a) where
  (SomeVec v1) == (SomeVec v2) = eqVec v1 v2
    where
      eqVec :: Eq a => Vec n a -> Vec m a -> Bool
      eqVec VNil VNil = True
      eqVec (VCons x xs) (VCons y ys) = x == y && eqVec xs ys
      eqVec _ _ = False

-- Convert SomeVec into a normal list
someVecToList :: SomeVec a -> [a]
someVecToList (SomeVec v) = go v
  where
    go :: Vec n a -> [a]
    go VNil         = []
    go (VCons x xs) = x : go xs

-- Compute the length of SomeVec
lengthSV :: SomeVec a -> Int
lengthSV (SomeVec v) = go v
  where
    go :: Vec n a -> Int
    go VNil         = 0
    go (VCons _ xs) = 1 + go xs