{-# LANGUAGE RankNTypes #-}

module RankN2 where

identity :: (forall a. a -> a) -> Int
identity f = f 1

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

identityTwoArgs :: (forall a. a -> a -> a) -> Int
identityTwoArgs f = f 1 2

threeArgs :: (forall a. a -> a -> a -> a) -> Int 
threeArgs f = f 1 2 3