{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where

import Data.List (minimumBy)

{-@ f ::[Int] -> (Int, {v:Int | v = 1}) @-}
f :: [Int] -> (Int, Int)
f = g

g   :: [Int] -> (Int, Int)
g cs = (minimumBy (\_ _ -> LT) cs, 1)