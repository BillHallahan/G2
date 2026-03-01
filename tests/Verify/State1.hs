{-# LANGUAGE CPP #-}

-- Largely from transformers package
-- https://hackage-content.haskell.org/package/transformers-0.6.3.0/docs/src/Control.Monad.Trans.State.Lazy.html#StateT

module StateMonad where

import Data.Functor.Identity
import Control.Applicative
import Control.Monad

-- ---------------------------------------------------------------------------
-- | A state transformer monad parameterized by:
--
--   * @s@ - The state.
--
--   * @m@ - The inner monad.
--
-- The 'return' function leaves the state unchanged, while @>>=@ uses
-- the final state of the first computation as the initial state of
-- the second.
newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }

type State s = StateT s Identity

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState :: State s a   -- ^state-passing computation to execute
         -> s           -- ^initial state
         -> (a, s)      -- ^return value and final state
runState m = runIdentity . runStateT m

simple1 :: State Int Int -> Bool
simple1 xs = runState xs 1 == runState (id xs) 1

simple1False :: State Int Int -> Bool
simple1False xs = runState xs 1 == runState (id xs) 2