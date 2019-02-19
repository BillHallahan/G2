Map-Reduce
==========

<div class="hidden">
\begin{code}
module MapReduce (mapReduce) where

import qualified Data.Map as M
import List
import Prelude hiding (map, reduce, concat, foldr, foldr1)
expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v
\end{code}
</div>

The following is a super simplified implementation of
[Map-Reduce](http://en.wikipedia.org/wiki/MapReduce)
using the [Lists](List.lhs) and `Data.Map`.

\begin{code}
mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v

mapReduce fm fr xs = kvm
  where
    kvs   = expand      fm xs     -- step 1
    kvsm  = group       kvs       -- step 2
    kvm   = collapse fr kvsm      -- step 3
\end{code}

**The Problem** If you solved `foldr1` then you should
get a single type error below, in the call to `foldr1`
in `collapse`. Fix the error by **modifying the
refinement type specifications** only (do not modify any code).

**Note:** This problem requires you to have solved the
`foldr1` problem from [List.lhs](List.lhs); otherwise
no points.

Next, we briefly describe and show each step of the
`mapReduce` function.

Step 1: Map Elements into Key-Value Lists
-----------------------------------------

\begin{code}
{-@ expand  :: (a -> List (k, v)) -> { xa : List a | size xa > 0 } -> List (k, v) @-}
expand f xs = concat (map f xs)
\end{code}

Step 2: Group By Key
--------------------

\begin{code}
{-@ group :: (Ord k) => { xkv : List (k, v) | size xkv > 0 } -> M.Map k { xv : (List v) | size xv > 0 } @-}
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = add v (M.findWithDefault empty k m)
\end{code}

Step 3: Reduce Each Key to Single Value
---------------------------------------

\begin{code}
{-@ collapse  :: (v -> v -> v) -> M.Map k { xv : (List v) | size xv > 0 } -> M.Map k v @-}
collapse f = M.map (foldr1 f)

toList :: M.Map k v -> List (k, v)
toList = M.foldrWithKey (\k v acc -> add (k, v) acc) empty
\end{code}

