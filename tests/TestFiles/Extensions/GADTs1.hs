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

instance Eq a => Eq (Expr a) where
  (Lit x) == (Lit y)         = x == y

  (Add a b) == (Add c d)     = a == c && b == d

  (IsZero e1) == (IsZero e2) = e1 == e2

  -- Compare condition and both branches
  (If c1 t1 f1) == (If c2 t2 f2) = c1 == c2 && t1 == t2 && f1 == f2

  -- If the constructors are different, the expressions are not equal
  _ == _ = False

eval :: Expr a -> a
eval (Lit n)       = n
eval (Add x y)     = eval x + eval y
eval (IsZero x)    = eval x == 0
eval (If cond t e) = if eval cond then eval t else eval e

exampleConditional :: Expr Int
exampleConditional = If (IsZero (Lit 0)) (Lit 42) (Lit 0)

evalEC :: Int
evalEC = eval exampleConditional

exampleExpr1 :: Expr Int
exampleExpr1 = Add (Lit 5) (Lit 3) -- 5 + 3

evalExpr1 :: Int 
evalExpr1 = eval exampleExpr1

exampleExpr2 :: Expr Bool
exampleExpr2 = IsZero (Add (Lit 2) (Lit (-2))) -- 2 + (-2) == 0

evalExpr2 :: Bool
evalExpr2 = eval exampleExpr2

exampleExpr3 :: Expr Int
exampleExpr3 = If (IsZero (Lit 0)) (Lit 10) (Lit 20) -- if 0 == 0 then 10 else 20

evalExpr3 ::  Int 
evalExpr3 = eval exampleExpr3

exampleExpr4 :: Expr Int
exampleExpr4 = If (IsZero (Lit 1)) (Lit 10) (Lit 20) -- if 1 == 0 then 10 else 20

evalExpr4 :: Int
evalExpr4 = eval exampleExpr4

exampleExpr5 :: Expr Bool
exampleExpr5 = IsZero (If (IsZero (Lit 0)) (Lit 0) (Lit 1)) -- isZero (if 0 == 0 then 0 else 1)

evalExpr5 :: Bool
evalExpr5 = eval exampleExpr5

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

-- Test cases for ArbValueGen 
data Contains a where
    CInt :: Contains Int
    CBool :: Contains Bool

instance Eq (Contains a) where
    CInt == CInt = True
    CBool == CBool = True

idCBool :: Contains Bool -> Contains Bool
idCBool x = x