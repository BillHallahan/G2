{-# LANGUAGE CPP #-}

-- From transformers package
-- https://hackage-content.haskell.org/package/transformers-0.6.3.0/docs/src/Control.Monad.Trans.State.Lazy.html#StateT

module TypeclassCode.State where

import Data.Functor.Identity

newtype State = StateT { runStateT :: Int -> Identity (Int, Int) }

runState :: State -> Int -> (Int, Int)
runState m x = runIdentity (runStateT m x)

p1 :: State -> Bool
p1 xs = runState xs 0 == runState xs 0