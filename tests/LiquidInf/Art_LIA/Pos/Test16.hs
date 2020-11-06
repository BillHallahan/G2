{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where

{-@ f :: { xs : Int | xs > 0 } @-}
f :: Int
f = empty (0, 0)

empty :: (Ord k) => (k, Int) -> Int
empty _ = 1