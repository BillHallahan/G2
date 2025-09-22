{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies, FlexibleInstances, FlexibleContexts, StandaloneDeriving #-}

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

instance Eq (Pairy a b c) where
  (PInt x)  == (PInt y)  = x == y
  (PBool x) == (PBool y) = x == y
  _         == _         = False


modifyPairy :: Pairy a b c -> Pairy a b c
modifyPairy (PInt n)  = PInt (n + 1)      -- increment Int
modifyPairy (PBool b) = PBool (not b)     -- flip Bool

pairyToInt :: Pairy a b c -> Int
pairyToInt (PInt n)  = if even n then 0 else 1
pairyToInt (PBool b) = if b then 1 else 0

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

-- GADT that have other GADT as parameter 
data Wrapper :: * -> * where
  WrapPairy :: Pairy a b c -> Wrapper (Pairy a b c)
  WrapInt   :: Int -> Wrapper Int

instance Eq (Wrapper t) where
  (WrapPairy p1) == (WrapPairy p2) = p1 == p2
  (WrapInt x)    == (WrapInt y)    = x == y
  _              == _              = False

-- Extract an Int from Wrapper if possible
unwrapWrapper :: Wrapper t -> Maybe Int
unwrapWrapper (WrapPairy (PInt n)) = Just n
unwrapWrapper (WrapPairy (PBool _)) = Nothing
unwrapWrapper (WrapInt n) = Just n

-- Increment contained Ints if possible
incrementWrapper :: Wrapper t -> Wrapper t
incrementWrapper (WrapPairy (PInt n)) = WrapPairy (PInt (n+1))
incrementWrapper (WrapPairy p@(PBool _)) = WrapPairy p
incrementWrapper (WrapInt n) = WrapInt (n+1)

-- Three refined parameters
data Tripley :: * -> * -> * -> * where
  Case1 :: Char   -> Tripley Int    Bool   String
  Case2 :: Double -> Tripley Bool   Char   Double
  Case3 :: [a]    -> Tripley [a]    [b]    [c]

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
newtype MyWrapInt = MyWrapInt Int 
    deriving (Eq, Show)

data Newty where
  MkNew :: MyWrapInt -> Newty 
deriving instance Eq Newty

unwrapNewty :: Newty -> Int
unwrapNewty (MkNew (MyWrapInt n)) = n

-- Here's the G2 output:
-- incrementNewty (MkNew ((coerce (0 :: Int)) :: WrapInt)) = MkNew ((coerce (1 :: Int)) :: WrapInt)
-- TODO: I know it's correct but is this a valid response we can show to the user?
incrementNewty :: Newty -> Newty
incrementNewty (MkNew (MyWrapInt n)) = MkNew (MyWrapInt (n + 1))

scaleNewty :: Int -> Newty -> Newty
scaleNewty factor (MkNew (MyWrapInt n)) = MkNew (MyWrapInt (n * factor))

isEvenNewty :: Newty -> Bool
isEvenNewty (MkNew (MyWrapInt n)) = n `mod` 2 == 0

-- Self-recursive and mutual GADTs
data Tree a where
  LeafInt  :: Int -> Tree Int
  LeafBool :: Bool -> Tree Bool
  Node     :: Tree a -> Tree a -> Tree a

data Forest a where
  FNil  :: Forest a
  FCons :: Tree a -> Forest a -> Forest a

-- Functions for testing
-- Warning: use small amount of steps fot the function below 
-- Sum all the Int leaves in a Tree Int
sumTree :: Tree Int -> Int
sumTree (LeafInt n)   = n
sumTree (Node l r)    = sumTree l + sumTree r

-- Count how many Bool leaves are True in a Tree Bool
countTrue :: Tree Bool -> Int
countTrue (LeafBool b) = if b then 1 else 0
countTrue (Node l r)   = countTrue l + countTrue r

-- Count the number of trees in a Forest
forestSize :: Forest a -> Int
forestSize FNil           = 0
forestSize (FCons _ rest) = 1 + forestSize rest

-- Map a function over a Tree (preserving type!)
mapTree :: (a -> a) -> Tree a -> Tree a
mapTree f (LeafInt n)     = LeafInt (f n)          -- works only if a ~ Int
mapTree f (LeafBool b)    = LeafBool (f b)         -- works only if a ~ Bool
mapTree f (Node l r)      = Node (mapTree f l) (mapTree f r)

-- introduce a new gadt that's empty or not empty 
-- this type basically determine something that's a tree or not