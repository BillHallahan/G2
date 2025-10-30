{-# LANGUAGE CPP, TypeApplications, ScopedTypeVariables #-}

module G2.Data.Utils ( uncurry3
                     , uncurry4

                     , fst4
                     , snd4
                     , thd4
                     , fth4

                     , holes
                     
                     , (==>)
                     
#if !(MIN_VERSION_base(4,18,0))
                     , mapAccumM
#endif

                     ) where

import Data.Bifunctor

#if !(MIN_VERSION_base(4,18,0))
import qualified Control.Monad.State.Lazy as CM
import Data.Coerce
#endif

-- * Tuples

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

uncurry4 :: (a -> b -> c -> d -> e) -> ((a, b, c, d) -> e)
uncurry4 f (a,b,c,d) = f a b c d

fst4 :: (a, b, c, d) -> a
fst4 (a, _, _, _) = a

snd4 :: (a, b, c, d) -> b
snd4 (_, b, _, _) = b

thd4 :: (a, b, c, d) -> c
thd4 (_, _, c, _) = c

fth4 :: (a, b, c, d) -> d
fth4 (_, _, _, d) = d

-- * Lists

-- | Compute all the ways of removing a single element from a list.
--
--  > holes [1,2,3] = [(1, [2,3]), (2, [1,3]), (3, [1,2])]
holes :: [a] -> [(a, [a])]
holes []     = []
holes (x:xs) = (x, xs) : (fmap . second) (x:) (holes xs)

-- * Logic

infixr 1 ==>
(==>) :: Bool -> Bool -> Bool
True ==> False = False
_ ==> _ = True

#if !(MIN_VERSION_base(4,18,0))
newtype StateT s m a = StateT { runStateT :: s -> m (s, a) }

-- | /Since: 4.18.0.0/
instance Monad m => Functor (StateT s m) where
    fmap = CM.liftM
    {-# INLINE fmap #-}

-- | /Since: 4.18.0.0/
instance Monad m => Applicative (StateT s m) where
    pure a = StateT $ \ s -> return (s, a)
    {-# INLINE pure #-}
    StateT mf <*> StateT mx = StateT $ \ s -> do
        (s', f) <- mf s
        (s'', x) <- mx s'
        return (s'', f x)
    {-# INLINE (<*>) #-}
    m *> k = m >>= \_ -> k
    {-# INLINE (*>) #-}

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce

-- | /Since: 4.18.0.0/
instance (Monad m) => Monad (StateT s m) where
    m >>= k  = StateT $ \ s -> do
        (s', a) <- runStateT m s
        runStateT (k a) s'
    {-# INLINE (>>=) #-}
    return = pure

mapAccumM
  :: forall m t s a b. (Monad m, Traversable t)
  => (s -> a -> m (s, b))
  -> s -> t a -> m (s, t b)
mapAccumM f s t = runStateT (mapM (StateT #. flip f) t) s
#endif
