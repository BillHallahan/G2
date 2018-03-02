Map-Reduce
==========

<div class="hidden">
\begin{code}
module MapReduce where

import qualified Data.Map as M
-- import List
import Prelude hiding (map, reduce, concat, foldr, foldr1)
group    :: List -> Map2 Int
\end{code}
</div>

--------------------

\begin{code}
data List = Emp
          | (:+:) Int List
              deriving (Eq, Ord, Show)

data T v = T v

data List2 v = Emp2 | C2 v (List2 v)

data Map2 v = Map2 (List2 (T v))

{-@ measure size      :: List -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1
  @-}



\end{code}


\begin{code}
{-@ group :: l:List -> Map2 ({l:Int | l>0}) @-}
group     = foldr2 (Map2 Emp2)

foldr2 :: Map2 Int -> List -> Map2 Int
foldr2 b Emp        = b
foldr2 b (x :+: xs) = b

\end{code}
