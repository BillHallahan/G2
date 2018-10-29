\begin{code}
module MapReduce (mapReduce) where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1)

mapReduce :: (Int -> Int)
          -> Int
mapReduce fm = length (expand fm)

{-@ expand  :: (Int -> Int) -> M.Map Int Int @-}
expand   :: (Int -> Int) -> M.Map Int Int
expand f = M.empty

\end{code}


