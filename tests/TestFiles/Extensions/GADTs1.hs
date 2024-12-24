{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies #-}

module GADTS1 where

import GHC.TypeLits 
import Data.Kind


-- infixr :>

-- data HList where 
--   Nil :: HList 
--   (:>) :: forall a . (Num a, Show a) => a -> HList -> HList

-- hlistHeadStr :: HList -> String
-- hlistHeadStr (x :> xs) = show (x + 1)

data MyList2 a = Nis | Conss a (MyList2 a)

lengthList2 :: MyList2 a -> Int
lengthList2 Nis       = 0
lengthList2 (Conss _ xs) = 1 + lengthList2 xs

-- this above is having an error that says
-- G2: No type found in typeWithStrName "MutVar#"
-- CallStack (from HasCallStack):
--   error, called at src/G2/Initialization/KnownValues.hs:127:10 in g2-0.2.0.0-inplace:G2.Initialization.KnownValues


data Expr a where
  Lit    :: Int -> Expr Int
  Add    :: Expr Int -> Expr Int -> Expr Int
  IsZero :: Expr Int -> Expr Bool
  If     :: Expr Bool -> Expr a -> Expr a -> Expr a

-- GADT that take multiple arguments 
exampleExpr :: Expr Int
exampleExpr = Add (Lit 5) (Lit 3)

exampleConditional :: Expr Int
exampleConditional = If (IsZero (Lit 0)) (Lit 42) (Lit 0)


data Peano = Succ Peano | Zero 

data Vec :: Peano -> Type -> Type where
    VNil  :: Vec Zero a
    VCons :: forall n a. a -> Vec n a -> Vec (Succ n) a

data TypedPair a b where
  Pair :: a -> b -> TypedPair a b

examplePair :: TypedPair Int String
examplePair = Pair 42 "hello"

data TypedTriple a b c where
  Triple :: a -> b -> c -> TypedTriple a b c 

exampleTriple :: TypedTriple Int String Bool
exampleTriple = Triple 32 "Hello" True

vecLength :: Vec n a -> Integer
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

vecTail :: Vec (Succ n) a -> Vec n a 
vecTail (VCons _ xs) = xs

-- Return all the elements of a list except the last one
vecInit :: Vec (Succ n) a -> Vec n a 
vecInit (VCons x VNil) = VNil 
vecInit (VCons x xs@(VCons y ys)) = VCons x (vecInit xs)


-- data Term a where
--     Lit :: Int ->  Term Int
--     Pair :: Term a -> Term b -> Term (a,b)

-- eval2 :: Term a -> a
-- eval2 (Lit i)     = i
-- eval2 (Pair a b)  = (eval2 a, eval2 b)

-- data X (b :: Bool) where
--     XTrue :: X b -> X True 
--     XFalse :: X False

-- getX :: X True
-- getX = walkX (XTrue XFalse)

eval2 :: Term a -> a
eval2 (Lit i)     = i
eval2 (Pair a b)  = (eval2 a, eval2 b)