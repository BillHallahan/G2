{-# LANGUAGE RankNTypes, KindSignatures #-}

module RankN2 where

import Data.Kind

--------- [Identity functions] ---------
identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

--------- [ADT Arguments] ---------
data Tree a = Leaf a | Inter (Tree a) (Tree a) deriving (Eq, Show)

treeArg :: (forall a. Tree a -> a) -> Int
treeArg f = f (Inter (Leaf 3) (Inter (Leaf 7) (Leaf 8)))

--------- [ADT Return Values] ---------
data Boxed a = Box a deriving (Eq, Show)

treeRet :: (forall a. a -> a -> Tree a) -> Tree Int
treeRet f = f 5 7

tupBoxRet :: (forall a b. a -> b -> (Boxed Int, (Boxed (Boxed b), Boxed (Boxed (Boxed a))))) -> (Boxed Int, (Boxed (Boxed Bool), Boxed (Boxed (Boxed Int))))
tupBoxRet f = f 5 False

listRet :: (forall a. a -> a -> [a]) -> [Int]
listRet f = f 4 5

literalRet :: (forall a. Boxed a -> a -> Int) -> Int
literalRet f = case f (Box 5) 23 of 
                5 -> 10
                4 -> 8
                _ -> 3

literalAndBoxedRet :: (forall a. a -> (Boxed Int, Boxed a)) -> Int
literalAndBoxedRet f = case f True of
                    (Box 2, Box True) -> 4
                    (Box 3, Box True) -> 6

mIntMaybe :: (forall m. m Int -> Maybe (m Int)) -> Maybe (Boxed Int)
mIntMaybe f = f (Box 4)

--------- [Function arguments] ---------
funcArg :: (forall a. (a -> a) -> a -> a) -> Int
funcArg f = f (\x -> x + 1) 3

funcArgBoxedArg :: (forall a. (Boxed a -> a) -> Boxed a -> a) -> Int
funcArgBoxedArg f = f (\(Box x) -> x) (Box 3)

funcArgBoxedLitArg :: (forall a. a -> (Boxed Int -> a -> a) -> a) -> Bool
funcArgBoxedLitArg f = f False (\(Box i) x -> x)

-- TODO: think about this
funcArgIntArgs :: (forall a. (Int -> Int -> a) -> a) -> Bool
funcArgIntArgs f = f (\x y -> x > 10 && y > 10)

funcArgWithTyToTyArg :: (forall m. (m Int -> Int) -> m Int -> Int) -> Int
funcArgWithTyToTyArg f = f (\(Box x) -> x) (Box 4)

--------- [Multiple function applications] ---------
twoApplicationsNeeded :: (forall a b c. (a -> b) -> (b -> c) -> a -> c) -> Int
twoApplicationsNeeded f = f (\x -> x) (\x -> x) 7

--------- [Polymorphic function type variable of kind * -> *] -----------
-- produces too many outputs with --n 200 because of cycling, removing cycling will reduce number of outputs
twoKindsToFrom :: (forall (a :: Type) m. m a -> (m a -> a) -> (a -> m a) -> m a) -> Boxed Int
twoKindsToFrom f = f (Box 4) (\(Box x) -> x) Box

--------- [Typeclasses - not handled yet] ---------
useTypeClass :: (forall a. (Num a) => a -> a) -> Int
useTypeClass f = f 8

-- This is Rank-3
funcArgNum :: ((forall b. (Num b) => b -> b) -> Int) -> Int
funcArgNum f = f (\x -> x + 1)
