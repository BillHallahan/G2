{-# LANGUAGE RecursiveDo #-}

module MonadFix where

import Control.Monad.Fix

justOnes :: Maybe [Int]
justOnes = mdo { xs <- Just (1:xs)
               ; return (map negate xs) }

nJustOnes :: Int -> Maybe [Int]
nJustOnes n = fmap (take n) justOnes

fac :: Int -> Int
fac = fix (\r n -> if n <= 1 then 1 else n * r (n-1))