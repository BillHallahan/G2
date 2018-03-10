Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- CHECKBINDER prop_size
-- CHECKBINDER empty
-- CHECKBINDER add
-- CHECKBINDER singleton
-- CHECKBINDER prop_replicate
-- CHECKBINDER prop_map
-- CHECKBINDER foldr1
-- CHECKBINDER prop_zipWith
-- CHECKBINDER prop_concat
 

module List ( List
            , empty
            , concat
            , fuu
            ) where

import Assert
import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

empty     :: List a
concat    :: List (List a) -> List a
\end{code}
</div>

A Sized List Datatype
---------------------

Lets cook up our own `List` data type from scratch:

\begin{code}
fuu :: List Int
fuu = concat empty

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ empty :: List a @-}
empty = Emp    

{-@ concat                  :: xss :  List (List a)  -> List a  @-}
concat (Emp :+: xss)         = Emp
concat ((x :+: xs) :+: xss)  = concat xss
\end{code}