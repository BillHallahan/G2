{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (foldr, map)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

map       :: (List Double -> b) -> List (List Double) -> List b
map f Emp        = Emp
map f (x :+: xs) = f x :+: Emp

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}

mapReduce :: (Ord k) => (List Double -> k) -> List (List Double) -> M.Map k Int
mapReduce fm xs = kvsm
  where
    kvs   = map fm xs
    kvsm  = foldr addKV  M.empty kvs

addKV k m = M.insert k 1 m

nearest   :: Int -> M.Map Int Point -> Point -> Int
kmeans1   :: Int -> Int -> List Point -> M.Map Int Point -> M.Map Int Int

-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}

{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}

{-@ nearest :: k:Nat -> M.Map (CenterK k) Point -> PointN k -> CenterK k @-}
nearest k centers p = fst $ minimumBy (\_ _ -> EQ) $ M.toList centers

{-@ kmeans1 :: k:Nat -> n:Nat ->
               List (PointN k) -> M.Map (CenterK k) Point -> M.Map (CenterK k) Int @-}
kmeans1 k n ps cs = mapReduce (nearest k cs) ps    
