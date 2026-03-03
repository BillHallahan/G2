{-# LANGUAGE CPP #-}

-- From transformers package
-- https://hackage-content.haskell.org/package/transformers-0.6.3.0/docs/src/Control.Monad.Trans.State.Lazy.html#StateT

module TypeclassCode.State where

import Control.Monad

import Data.Coerce

data Identity a = Identity { runIdentity :: a }

instance Functor Identity where
    fmap f (Identity x)   = Identity (f x)

instance Applicative Identity where
    pure     = Identity
    (Identity f) <*> (Identity x)    = Identity (f x)

instance Monad Identity where
    m >>= k  = k (runIdentity m)

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
data StateT s m a = StateT { runStateT :: s -> m (a,s) }

type State s = StateT s Identity

-- | Unwrap a state monad computation as a function.
-- (The inverse of 'state'.)
runState :: State s a   -- ^state-passing computation to execute
         -> s           -- ^initial state
         -> (a, s)      -- ^return value and final state
runState m = runIdentity . runStateT m

(<**>) :: Monad m => StateT s m (t -> a) -> StateT s m t -> StateT s m a
StateT mf <**> StateT mx = StateT $ \ s -> do
    ~(f, s') <- mf s
    ~(x, s'') <- mx s'
    return (f x, s'')
infixl 4 <**>

r :: a -> State s a
r a = StateT $ \ s -> return (a, s)

p1 :: State Int (Int -> Int) -> Bool
p1 u = runState (r (.) <**> u <**> (r (\_ -> 1)) <**> r 0) 0 == runState (u <**> ((r (\_ -> 1)) <**> r 0)) 0
