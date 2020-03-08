-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

data D a = Emp
         | R a
         deriving (Eq, Ord, Show)

{-@ f :: D { x:Int | 0 <= x} -> M.Map {v:Int | 0 <= v } Int @-}
f :: D Int -> M.Map Int Int
f xs = M.map (\x -> 1) (g h M.empty xs)

g :: (a -> b -> b) -> b -> D a -> b
g _  b Emp = b
g op b (R x) = x `op` b

h :: Int -> M.Map Int (D Int) -> M.Map Int (D Int)
h k m = M.insert k (R 1) m