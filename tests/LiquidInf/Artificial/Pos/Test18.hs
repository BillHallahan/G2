-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

data D a = Emp
         | R a
         deriving (Eq, Ord, Show)

{-@ f :: D { x:Int | 0 <= x} -> M.Map {v:Int | 0 <= v } (D Int) @-}
f :: D Int -> M.Map Int (D Int)
f x = g x

g :: D Int -> M.Map Int (D Int)
g _ = M.empty