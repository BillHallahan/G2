{-# LANGUAGE RankNTypes #-}

module RankN2 where

identity :: (forall a. a -> a) -> Int
identity f = f 1

twoArgs :: (forall a. a -> a -> a) -> Int
twoArgs f = f 1 2

intArg :: (forall a. Int -> a -> a) -> Int
intArg f = f 1 2

intArg2 :: (forall a. Int -> a -> a -> a) -> Int
intArg2 f = f 1 2 3

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

identityTwoArgs :: (forall a. a -> a -> a) -> Int
identityTwoArgs f = f 1 2

threeArgs :: (forall a. a -> a -> a -> a) -> Int 
threeArgs f = f 1 2 3

data Boxed a = Box a

adt_arg :: (forall a. Boxed a -> a) -> Int
adt_arg f = f (Box 1)