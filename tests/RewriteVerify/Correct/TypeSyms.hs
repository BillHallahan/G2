{-# LANGUAGE GeneralizedNewtypeDeriving, UnboxedTuples #-}

module Control.Parallel.Strategies where

import Control.Monad.Fix (MonadFix (..))

type Strategy a = a -> IO a

usingIO :: Strategy Int -> IO Int
usingIO strat = strat 1

f :: Strategy [Int]
f xs0 = return xs0

g :: Int -> Strategy [Int]
g n0 xs0 = return xs0

{-# RULES "parBuffer"   forall n . g n = f #-}

