{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies #-}

module GADTS1 where


import GHC.TypeLits 
import Data.Kind

data ShapeType = Circle | Rectangle

data Shape where
  CircleShape :: Double -> Shape
  RectangleShape :: Double -> Double -> Shape

area :: Shape -> Double
area (CircleShape radius) = pi * radius * radius
area (RectangleShape width height) = width * height

infixr :>

data HList where 
  Nil :: HList 
  (:>) :: forall a . (Num a, Show a) => a -> HList -> HList

hlistHeadStr :: HList -> String
hlistHeadStr (x :> xs) = show (x + 1)

data MyList a where
  Ni :: MyList a
  Cons :: a -> MyList a -> MyList a

-- recursion on recursive GADT 
lengthList :: MyList a -> Int
lengthList Ni        = 0
lengthList (Cons _ xs) = 1 + lengthList xs

add2 :: a -> a -> MyList a -> MyList a
add2 a1 a2 li = Cons a2 $ Cons a1 li  

addn :: [a] -> MyList a -> MyList a 
addn  [] a = a 
addn (x:xs) a = addn xs (Cons x a) 

data MyExpr a where 
  Lt :: Int -> MyExpr Int 
  Mul :: MyExpr Int -> MyExpr Int ->  MyExpr Int
  Add :: MyExpr Int -> MyExpr Int ->  MyExpr Int

evalMyExpr :: MyExpr a -> a
evalMyExpr (Lt a) = a
evalMyExpr (Mul a1 a2) = evalMyExpr a1 * evalMyExpr a2 
evalMyExpr (Add a1 a2) = evalMyExpr a1 + evalMyExpr a2 

testeval :: Int -> MyExpr Int 
testeval a1 = testeval $ evalMyExpr $ Lt (2*a1)


checkeq :: Eq a => a -> a -> Bool
checkeq a a1 = a == a1

id2 :: a -> a 
id2 x = x


data Peano = Succ Peano | Zero 

data Vec :: Peano -> Type -> Type where
    VNil  :: Vec Zero a
    VCons :: forall n a. a -> Vec n a -> Vec (Succ n) a

vecLength :: Vec n a -> Integer
vecLength VNil         = 0
vecLength (VCons _ xs) = 1 + vecLength xs

vecHead :: Vec (Succ n) a -> a 
vecHead (VCons x _) = x

vecZip :: Vec n a -> Vec n b -> Vec n (a, b)
vecZip VNil _ =  VNil 
vecZip (VCons x xs) (VCons y ys) = VCons (x, y) (vecZip xs ys)


data Term a where
    Lit :: Int ->  Term Int
    Pair :: Term a -> Term b -> Term (a,b)

eval2 :: Term a -> a
eval2 (Lit i)     = i
eval2 (Pair a b)  = (eval2 a, eval2 b)
