module NonEmpty where

import Control.Applicative

data NonEmpty a = NE a [a]

instance Eq a => Eq (NonEmpty a) where
    NE x xs == NE y ys = x == y && xs == ys

instance Functor NonEmpty where
  fmap f (NE a as) = NE (f a) (fmap f as)
  b <$ (NE _ as)   = NE b (b <$ as)

instance Applicative NonEmpty where
  pure a = NE a []
  (<*>) = ap
  liftA2 = liftM2

instance Monad NonEmpty where
  (NE a as) >>= f = NE b (bs ++ bs')
    where NE b bs = f a
          bs' = as >>= toList . f
          toList (NE c cs) = c : cs

ap                :: (Monad m) => m (a -> b) -> m a -> m b
ap m1 m2          = do { x1 <- m1; x2 <- m2; return (x1 x2) }

liftM2  :: (Monad m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2 f m1 m2          = do { x1 <- m1; x2 <- m2; return (f x1 x2) }

prop :: Eq a => NonEmpty a -> Bool
prop v = ((NE id []) `ap` v) == v
