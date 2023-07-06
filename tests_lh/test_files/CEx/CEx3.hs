{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test51 ( List, kmeans1) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import qualified Data.Map as M

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

foldr1 op (x :+: xs) = x
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

type Point   = List Double

{-@ kmeans1 :: n:Nat -> M.Map Int (List Point) -> (M.Map Int Point) @-}
kmeans1   :: Int -> M.Map Int (List Point) -> M.Map Int Point
kmeans1 n ps = M.map (\p -> p) (M.map (foldr1 (\y _ -> y)) ps)