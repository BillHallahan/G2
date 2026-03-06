{-# LANGUAGE CPP #-}

-- From transformers package
-- https://hackage-content.haskell.org/package/transformers-0.6.3.0/docs/src/Control.Monad.Trans.State.Lazy.html#StateT

module TypeclassCode.Reader where

import Data.Functor.Identity
import Control.Applicative
import Control.Monad

-- | The reader monad transformer,
-- which adds a read-only environment to the given monad.
--
-- The 'return' function ignores the environment, while @m '>>=' k@
-- passes the inherited environment to both subcomputations:
--
-- <<images/bind-ReaderT.svg>>
--
--
-- @ReaderT r m@ is strict if and only if @m@ is.
newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

-- | The parameterizable reader monad, which is non-strict.
--
-- Computations are functions of a shared environment.
--
-- The 'return' function ignores the environment, while @m '>>=' k@
-- passes the inherited environment to both subcomputations:
--
-- <<images/bind-ReaderT.svg>>
--
type Reader r = ReaderT r Identity

-- | Runs a @Reader@ and extracts the final value from it.
-- (The inverse of 'reader'.)
runReader
    :: Reader r a       -- ^ A @Reader@ to run.
    -> r                -- ^ An initial environment.
    -> a
runReader m = runIdentity . runReaderT m
{-# INLINE runReader #-}

-- | Transform the computation inside a @ReaderT@.
--
-- * @'runReaderT' ('mapReaderT' f m) = f . 'runReaderT' m@
mapReaderT :: (m a -> n b) -> ReaderT r m a -> ReaderT r n b
mapReaderT f m = ReaderT $ f . runReaderT m
{-# INLINE mapReaderT #-}

instance (Functor m) => Functor (ReaderT r m) where
    fmap f  = mapReaderT (fmap f)
    {-# INLINE fmap #-}
    x <$ v = mapReaderT (x <$) v
    {-# INLINE (<$) #-}

instance (Applicative m) => Applicative (ReaderT r m) where
    pure    = liftReaderT . pure
    {-# INLINE pure #-}
    f <*> v = ReaderT $ \ r -> runReaderT f r <*> runReaderT v r

liftReaderT :: m a -> ReaderT r m a
liftReaderT m = ReaderT (const m)
{-# INLINE liftReaderT #-}

p1 :: Reader Int (Int -> Int) -> Reader Int (Int -> Int) -> Reader Int Int -> Bool
p1 u v w = runReader (pure (.) <*> u <*> v <*> w) 0 == runReader (u <*> (v <*> w)) 0

p1False :: Reader Int (Int -> Int) -> Reader Int (Int -> Int) -> Reader Int Int -> Bool
p1False u v w = runReader (pure (.) <*> u <*> v <*> w) 1 == runReader (u <*> (v <*> w)) 0
