{-@ LIQUID "--no-termination" @-}

module SetInsert (Set (..), prop) where

import Data.Set

prop :: Int -> Set Int -> Set Int
prop = f

f :: Int -> Set Int -> Set Int
f = insert