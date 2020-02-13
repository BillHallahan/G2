{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

import Data.List (minimumBy)

data List a = Emp | R a deriving (Eq, Ord, Show)

{-@ measure size :: List a -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListNE a = {v:List a | size v > 0} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

-- | N-Dimensional Point
type Point   = List Int

{-@ type PointN N = ListN Int N @-}

{-@ m :: (a -> b) -> xa : List a -> List b @-}
m :: (a -> b) -> List a -> List b
m f Emp = Emp
m f (R x) = R (f x)

f :: (a -> b -> b) -> b -> List a -> b
f _  b Emp = b
f op b (R x) = x `op` b

{-@ k :: List (PointN 1) -> [Int] -> M.Map {v:Int | 0 <= v } Int @-}
k :: List Point -> [Int] -> M.Map Int Int
k ps cs = r cs ps

{-@ r ::  [Int] -> List (List Int) -> M.Map Int Int @-}
r :: [Int] -> List (List Int) -> M.Map Int Int
r cs xs = kvm
  where
    kvs   = m (\_ -> minimumBy (\_ _ -> EQ) cs) xs
    kvsm  = f (\k _ -> a k) M.empty kvs
    kvm   = M.map (\_ -> 0) kvsm

{-@ a :: Int -> M.Map Int (List Int) @-}
a :: Int -> M.Map Int (List Int)
a k = M.insert k (R 1) M.empty
