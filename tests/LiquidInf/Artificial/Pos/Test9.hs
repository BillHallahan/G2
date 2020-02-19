{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import Prelude hiding (foldr, foldr1, map)

import qualified Data.Map as M
import Data.List (minimumBy)

{-@ c :: [{v:Int | 0 <= v }] -> {v:Int | 0 <= v } @-}
c :: [Int] -> Int
c m = g m

g :: [Int] -> Int
g m = minimumBy (\_ _ -> LT) $ m
