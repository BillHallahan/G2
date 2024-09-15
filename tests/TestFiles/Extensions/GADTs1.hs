{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes, TypeFamilies #-}

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

idlr :: Either l r -> Either l r 
idlr x = x

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

vecZipConc :: Vec (Succ Zero) (Int, Char)
vecZipConc = vecZip (VCons 1 VNil) (VCons 'a' VNil) 

vecMap :: (a -> b) -> Vec n a -> Vec n b 
vecMap _ VNil = VNil 
vecMap f (VCons x xs) = VCons (f x) (vecMap f xs)

vecTail :: Vec (Succ n) a -> Vec n a 
vecTail (VCons _ xs) = xs

-- Return all the elements of a list except the last one
vecInit :: Vec (Succ n) a -> Vec n a 
vecInit (VCons x VNil) = VNil 
vecInit (VCons x xs@(VCons y ys)) = VCons x (vecInit xs)


data Term a where
    Lit :: Int ->  Term Int
    Pair :: Term a -> Term b -> Term (a,b)

eval2 :: Term a -> a
eval2 (Lit i)     = i
eval2 (Pair a b)  = (eval2 a, eval2 b)