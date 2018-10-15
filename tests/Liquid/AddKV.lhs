K-Means Clustering
==================


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans where

import Data.List (minimumBy)
import Prelude hiding (map, repeat, foldr, zipWith, concat, foldr1)
import qualified Data.Map as M


\end{code}
</div>

Next, lets use our `MapReduce` library to implement
[K-Means Clustering](http://en.wikipedia.org/wiki/K-means_clustering)


Points and Clusters
-------------------

First, lets define the various types that model the key entities in clustering.

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ empty :: List a @-}
empty = Emp

addKV (k,v) m = M.insert k (v :+: empty) m

\end{code}

