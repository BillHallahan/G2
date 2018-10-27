\begin{code}
module MapReduce (mapReduce) where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1)

mapReduce :: (Int -> Int)
          -> Int
mapReduce fm = length kvs
  where
    kvs      = expand      fm     -- step 1

{-@ expand  :: (Int -> Int) -> M.Map Int Int @-}
expand   :: (Int -> Int) -> M.Map Int Int
expand f = M.empty

\end{code}


