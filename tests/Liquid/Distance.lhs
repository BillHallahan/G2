K-Means Clustering
==================


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans where

import Data.List (minimumBy)
import Prelude hiding (map, repeat, foldr, zipWith)
import qualified Data.Map as M

distance :: Int -> Point -> Point -> Double
\end{code}
</div>

\begin{code}
data List a = Emp
            | (:+:) a (List a)


{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}


-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}

type Center  = Int
{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}

type Centering = M.Map Center Point
{-@ type CenteringKN K N = M.Map (CenterK K) (PointN N) @-}

type Cluster = (Int, Point)

{-@ type ClusterN N = (Pos, PointN N) @-}
{-@ type Pos        = {v:Int | v > 0} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ zipWith :: (a -> b -> c) -> xs:List a -> ListX b xs -> ListX c xs @-}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ distance :: n:Nat -> x:List Double -> {y:List Double | y > x} -> Double @-}
distance n px py = foldr (+) 0 $ zipWith (\x y -> x) px py

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ f :: n:Nat -> x:Double -> {y:Double | y > 0} -> Double @-}
f :: Int -> Double -> Double -> Double
f n px py = px


\end{code}
