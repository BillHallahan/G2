
module Combined ( List
                , kmeans1) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

map       :: (a -> b) -> List a -> List b
map f Emp        = Emp
map f (x :+: xs) = f x :+: Emp

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` b

addKV (k,v) m = M.insert k v m

divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n

-- | N-Dimensional Point
type Point   = List Double

nearest   :: M.Map Int Point -> Int
nearest centers = fst $ minimumBy (\_ _ -> LT) (M.toList centers)

centroid :: Point -> Int -> Point
centroid p sz = map (\x -> x `divide` sz) p

{-@ kmeans1 :: List ({v:List Double | size v = 1}) -> M.Map {v:Int | 0 <= v } Point -> M.Map {v:Int | 0 <= v } Point @-}
kmeans1   :: List Point -> M.Map Int Point -> M.Map Int Point
kmeans1 ps cs = normalize newClusters
  where
    normalize     :: M.Map a (Int, Point) -> M.Map a Point
    normalize     = M.map (\(sz, p) -> centroid p 1)
    newClusters   = foldr addKV  M.empty       (map      fm ps)
    fm p          = (nearest cs, (1 :: Int, p))
