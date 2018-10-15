K-Means Clustering
==================


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans where

import Data.List (minimumBy)
import Assert
import List
import Prelude hiding (map, repeat, foldr, zipWith, concat, foldr1)
import qualified Data.Map as M

group    :: (Ord k) => List (k, v) -> M.Map k (List v)

\end{code}
</div>

Next, lets use our `MapReduce` library to implement
[K-Means Clustering](http://en.wikipedia.org/wiki/K-means_clustering)


Points and Clusters
-------------------

First, lets define the various types that model the key entities in clustering.

\begin{code}

{-@ group :: (Ord k) => List (k, v) -> M.Map k (List v) @-}
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k (add v empty) m
  

\end{code}

