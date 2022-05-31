{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
 
module Combined (f) where

import qualified Data.Map as M

{-@ f :: Nat -> M.Map Int {v: Int | v = 1} -> M.Map Int {v: Int | v = 1} @-}
f :: Int -> M.Map Int Int -> M.Map Int Int
f s = r s g

r :: Int -> (a -> a) -> a -> a
r 0 f x = x
r n f x = r (n-1) f (f x)

g :: M.Map Int Int -> M.Map Int Int
g cs = M.empty
