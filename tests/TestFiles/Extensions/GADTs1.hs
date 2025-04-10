{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module GADTS1 where

import GHC.TypeLits 
import Data.Kind

-- example of recursive GADT
data Expr a where
  Lit    :: Int -> Expr Int
  Add    :: Expr Int -> Expr Int -> Expr Int
  IsZero :: Expr Int -> Expr Bool
  If     :: Expr Bool -> Expr a -> Expr a -> Expr a

instance Eq (Expr a) where
  (Lit x) == (Lit y) = x == y
  
  (Add e1 e2) == (Add e3 e4) = e1 == e3 && e2 == e4
  
  (IsZero e1) == (IsZero e2) = e1 == e2
  
  (If c1 t1 f1) == (If c2 t2 f2) = c1 == c2 && t1 == t2 && f1 == f2
  
  -- If the constructors are different, the expressions are not equal
  _ == _ = False

eval :: Expr a -> a
eval (Lit n)       = n
eval (Add x y)     = eval x + eval y
eval (IsZero x)    = eval x == 0
eval (If cond t e) = if eval cond then eval t else eval e


data Peano = Succ Peano | Zero 

data Vec :: Peano -> Type -> Type where
    VNil  :: Vec Zero a
    VCons :: forall n a. a -> Vec n a -> Vec (Succ n) a

instance Eq a => Eq (Vec Zero a) where
    VNil == VNil = True

instance (Eq a, Eq (Vec n a)) => Eq (Vec (Succ n) a) where
    (VCons x xs) == (VCons y ys) = x == y && xs == ys

vecLength :: Vec n a -> Int
vecLength VNil         = 0
vecLength (VCons _ xs) = 1 + vecLength xs

vecHead :: Vec (Succ n) a -> a 
vecHead (VCons x _) = x

vecZip :: Vec n a -> Vec n b -> Vec n (a, b)
vecZip VNil _ =  VNil 
vecZip (VCons x xs) (VCons y ys) = VCons (x, y) (vecZip xs ys)

vecZipConc :: Vec (Succ Zero) (Int, Char)
vecZipConc = vecZip (VCons 1 VNil) (VCons 'a' VNil) 

vecZipConc2 :: Vec (Succ (Succ Zero)) (Int, Char)
vecZipConc2 = vecZip (VCons 1 (VCons 2 VNil)) (VCons 'a' (VCons 'b' VNil)) 

vecMap :: (a -> b) -> Vec n a -> Vec n b 
vecMap _ VNil = VNil 
vecMap f (VCons x xs) = VCons (f x) (vecMap f xs)

vecHeadEx :: Int
vecHeadEx = vecHead (VCons 1 (VCons 2 VNil))

-- have to run 400 steps for the result to show up instead of 200
doubleVec :: Vec (Succ (Succ Zero)) Int
doubleVec = vecMap (*2) (VCons 1 (VCons 2 VNil))

vecTail :: Vec (Succ n) a -> Vec n a 
vecTail (VCons _ xs) = xs

tailVec :: Vec (Succ Zero) Char
tailVec = vecTail (VCons 'a' (VCons 'b' VNil)) 

tailPairVec :: Vec (Succ Zero) (Int, Char)
tailPairVec = vecTail $ vecZip (VCons 1 (VCons 2 VNil)) (VCons 'a' (VCons 'b' VNil)) 

-- Return all the elements of a list except the last one
vecInit :: Vec (Succ n) a -> Vec n a 
vecInit (VCons x VNil) = VNil 
vecInit (VCons x xs@(VCons y ys)) = VCons x (vecInit xs)
