{-# LANGUAGE CPP #-}

-- From transformers package
-- https://hackage-content.haskell.org/package/transformers-0.6.3.0/docs/src/Control.Monad.Trans.State.Lazy.html#StateT

module State4 where

import Control.Applicative
import Control.Monad

newtype Identity a = Identity { runIdentity :: a }

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

instance (Functor m) => Functor (StateT s m) where
    fmap f m = StateT $ \ s ->
        fmap (\ ~(a, s') -> (f a, s')) $ runStateT m s
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (StateT s m) where
    pure a = StateT $ \ s -> return (a, s)
    {-# INLINE pure #-}
    StateT mf <*> StateT mx = StateT $ \ s -> do
        ~(f, s') <- mf s
        ~(x, s'') <- mx s'
        return (f x, s'')
    {-# INLINE (<*>) #-}

p1 :: State Int (a1 -> Int) -> State Int (a2 -> a1) -> State Int a2 -> Bool
p1 u v w = runState (pure (.) <*> u <*> v <*> w) 0 == runState (u <*> (v <*> w)) 0

