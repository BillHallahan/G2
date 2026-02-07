{-# LANGUAGE RankNTypes #-}

module RankN2 where

identity :: (forall a. a -> a) -> Int
identity f = f 1

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1