Map-Reduce
==========

<div class="hidden">
\begin{code}
module MapReduce (List, expand) where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1)
expand   :: (a -> List a) -> List a -> List a
concat    :: List (List a) -> List a
\end{code}
</div>

The following is a super simplified implementation of
[Map-Reduce](http://en.wikipedia.org/wiki/MapReduce)
using the [Lists](List.lhs) and `Data.Map`.



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


data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ expand  :: (a -> List a) -> List a -> List a @-}
expand f xs = concat Emp

    

{-@ concat                  :: xss :  List (List a) 
                            -> List a @-}
concat (Emp :+: xss)         = Emp
\end{code}
