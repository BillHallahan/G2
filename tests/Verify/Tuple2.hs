module Tuple2 where

import qualified GHC.List as List
import Data.Coerce

prop :: [(Sum Int, A)] -> Bool
prop xs = mconcat xs == foldr (<>) mempty xs

data A = A

instance Eq A where
    A == A = True

instance Semigroup A where
    A <> A = A

instance Monoid A where
        -- Should it be strict?
        mempty        = A
        mconcat _     = A

newtype Sum a = Sum { getSum :: a }
        -- deriving ( Eq       -- ^ @since base-2.01
        --          , Ord      -- ^ @since base-2.01
        --          , Read     -- ^ @since base-2.01
        --          , Show     -- ^ @since base-2.01
        --          , Bounded  -- ^ @since base-2.01
        --          , Generic  -- ^ @since base-4.7.0.0
        --          , Generic1 -- ^ @since base-4.7.0.0
        --          , Num      -- ^ @since base-4.7.0.0
        --          )

instance Eq a => Eq (Sum a) where
    Sum x == Sum y = x == y

instance Num a => Semigroup (Sum a) where
        (<>) = coerce ((+) :: a -> a -> a)

-- | @since base-2.01
instance Num a => Monoid (Sum a) where
        mempty = Sum (fromInteger 0)
        -- By default, we would get a lazy right fold. This forces the use of a strict
        -- left fold instead.
        mconcat = List.foldl' (<>) mempty
        {-# INLINE mconcat #-}

