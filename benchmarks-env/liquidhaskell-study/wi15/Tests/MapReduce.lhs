Map-Reduce
==========

<div class="hidden">
\begin{code}
module MapReduce (mapReduce) where

import qualified Data.Map as M
import List2
import Prelude hiding (map, reduce, concat, foldr, foldr1)
group    :: M.Map Int (List Int)
collapse :: (Int -> Int -> Int) -> M.Map Int (List Int) -> M.Map Int Int
\end{code}
</div>

The following is a super simplified implementation of
[Map-Reduce](http://en.wikipedia.org/wiki/MapReduce)
using the [Lists](List.lhs) and `Data.Map`.

\begin{code}
mapReduce :: (Int -> List (Int, Int))
                     -> (Int -> Int -> Int)
                     -> M.Map Int Int

mapReduce fm fr = kvm
  where
    kvsm     = group              -- step 2
    kvm      = if length (M.elems kvsm) > 0
                 then collapse fr kvsm      -- step 3
                 else error "Must have a non empty list"
\end{code}


Step 2: Group By Key
--------------------

\begin{code}
{-@ group :: M.Map Int (List Int) @-}
group     = M.empty

\end{code}

Step 3: Reduce Each Key to Single Value
---------------------------------------

\begin{code}
{-@ collapse  :: (Int -> Int -> Int) -> M.Map Int (List Int) -> M.Map Int Int @-}
collapse f _= M.empty

\end{code}

