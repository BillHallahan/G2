\begin{code}

module WhereFuncs where

-- import MapReduce
import Prelude hiding (map, repeat, foldr, zipWith, foldr1, concat)
import qualified Data.Map as M

type C = M.Map Int Int

{-@ f :: C -> C
  @-}
f :: C -> C
f cs = normalize newClusters
  where
    normalize     :: M.Map a Int -> M.Map a Int
    normalize _   = M.empty 
    newClusters   = M.empty

{-@ g :: M.Map Int Int -> M.Map Int Int
  @-}
g :: M.Map Int Int -> M.Map Int Int
g cs = normalize
  where
    normalize :: M.Map a Int
    normalize = M.empty 
\end{code}