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
    m *> k = m >>= \_ -> k
    {-# INLINE (*>) #-}

instance (Functor m, MonadPlus m) => Alternative (StateT s m) where
    empty = StateT $ \ _ -> mzero
    {-# INLINE empty #-}
    StateT m <|> StateT n = StateT $ \ s -> m s `mplus` n s
    {-# INLINE (<|>) #-}

instance (Monad m) => Monad (StateT s m) where
#if !(MIN_VERSION_base(4,8,0))
    return a = StateT $ \ s -> return (a, s)
    {-# INLINE return #-}
#endif
    m >>= k  = StateT $ \ s -> do
        ~(a, s') <- runStateT m s
        runStateT (k a) s'
    {-# INLINE (>>=) #-}
#if !(MIN_VERSION_base(4,13,0))
    fail str = StateT $ \ _ -> fail str
    {-# INLINE fail #-}
#endif

simple1 :: State Int Int -> Bool
simple1 xs = runState xs 1 == runState (id xs) 1

simple1False :: State Int Int -> Bool
simple1False xs = runState xs 1 == runState (id xs) 2

p1 :: (Int -> Int) -> State Int Int -> Bool
p1 f xs = runState (fmap (f . f) (return 1)) 1 == runState ((fmap f . fmap f) (return 1)) 1

p1False :: (Int -> Int) -> State Int Int -> Bool
p1False f xs = runState (fmap (f . f) (return 1)) 1 == runState ((fmap f) (return 1)) 1
