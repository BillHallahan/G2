{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module GADTs3 where

import GHC.TypeLits hiding (Nat)
import Data.Kind

-- This file aims to provide more test cases that are different than the 
-- test cases in GADTs1 and 2 ensure that GADT works with G2

-- Baseline GADT
data Expr a where
  I  :: Int  -> Expr Int
  B  :: Bool -> Expr Bool
  If :: Expr Bool -> Expr a -> Expr a -> Expr a

evalExpr :: Expr a -> a
evalExpr (I n)       = n
evalExpr (B b)       = b
evalExpr (If c x y)  = if evalExpr c then evalExpr x else evalExpr y

-- Refined parameter that is itself a GADT
data Box g where
  MkBox :: g a -> Box g

showBoxExpr :: Box Expr -> String
showBoxExpr (MkBox (I n))  = "Boxed Int " ++ show n
showBoxExpr (MkBox (B b))  = "Boxed Bool " ++ show b
showBoxExpr (MkBox (If _ _ _)) = "Boxed If"

-- Vec-like GADT with refined Nat parameter
data Nat = Z | S Nat

data Vec :: * -> Nat -> * where
  Nil  :: Vec a 'Z
  Cons :: a -> Vec a n -> Vec a ('S n)

vecHead :: Vec a n -> Maybe a
vecHead Nil        = Nothing
vecHead (Cons x _) = Just x

-- Two refined parameters
data Pairy :: * -> * -> * -> * where
  PInt  :: Int  -> Pairy Int  Bool String
  PBool :: Bool -> Pairy Bool Char Double

-- G2: evalVar: bad input.Id (Name "$fShowBool" (Just "GHC.Show")
showPairy :: Pairy a b c -> String
showPairy (PInt n)  = "Int: "  ++ show n
showPairy (PBool b) = "Bool: " ++ show b

pairyTag :: Pairy a b c -> Int
pairyTag (PInt _)  = 1
pairyTag (PBool _) = 2

pairyValue :: Pairy a b c -> Either Int Bool
pairyValue (PInt n)  = Left n
pairyValue (PBool b) = Right b

combinePairy :: Pairy a b c -> Pairy a b c -> Either Int Bool
combinePairy (PInt x)  (PInt y)  = Left (x + y)      -- sum the Ints
combinePairy (PBool x) (PBool y) = Right (x && y)     -- logical AND for Bools
combinePairy _ _ = error "Cannot combine different constructors"

-- Three refined parameters
data Tripley :: * -> * -> * -> * where
  Case1 :: Char   -> Tripley Int    Bool   String
  Case2 :: Double -> Tripley Bool   Char   Double
  Case3 :: [a]    -> Tripley [a]    [b]    [c]

-- it seems like show is generally having a problem in validation and inst-after
showTripley :: Show a => Tripley a b c -> String
showTripley (Case1 ch) = "Char: "   ++ show ch
showTripley (Case2 d)  = "Double: " ++ show d
showTripley (Case3 xs) = "List length: " ++ show (length xs)

sizeTripley :: Tripley a b c -> Int
sizeTripley (Case1 _)  = 1
sizeTripley (Case2 _)  = 1
sizeTripley (Case3 xs) = length xs

-- Refined parameter that is polymorphic
data WrapPoly f a where
  MkWrap :: f a -> WrapPoly f a

unwrapMaybe :: WrapPoly Maybe a -> Maybe a
unwrapMaybe (MkWrap x) = x

-- Refined parameter that is a newtype
newtype WrapInt = WrapInt Int

data Newty where
  MkNew :: WrapInt -> Newty

unwrapNewty :: Newty -> Int
unwrapNewty (MkNew (WrapInt n)) = n

-- Self-recursive and mutual GADTs
data Tree a where
  Leaf :: a -> Tree a
  Node :: Tree a -> Tree a -> Tree a

data Forest a where
  FNil  :: Forest a
  FCons :: Tree a -> Forest a -> Forest a

-- mutual GADT is running way too long and it have its process being killed 
countLeaves :: Tree a -> Int
countLeaves (Leaf _)   = 1
countLeaves (Node l r) = countLeaves l + countLeaves r

forestSize :: Forest a -> Int
forestSize FNil         = 0
forestSize (FCons t ts) = countLeaves t + forestSize ts

-- GADT wrapped in a newtype
data Funny a where
  FunnyInt :: Int -> Funny Int

newtype NF = NF (Funny Int)

unNF :: NF -> Int
unNF (NF (FunnyInt n)) = n