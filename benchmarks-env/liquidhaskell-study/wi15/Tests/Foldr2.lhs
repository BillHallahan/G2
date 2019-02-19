
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
 

module List  where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

\end{code}
</div>


A Sized List Datatype
---------------------

Lets cook up our own `List` data type from scratch:

\begin{code}


data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}
\end{code}

It will be helpful to have a few abbreviations. First,
lists whose size is equal to `N`

\begin{code}
{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}
\end{code}


\begin{code}

{-@ foldr :: (b -> b -> b) -> b-> {xs:List b | size xs > 0 } -> b @-}
foldr :: (b -> b -> b) -> b -> List b -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b Emp)
-- foldr op b (x :+: xs) = x `op` (foldr op b Emp)
\end{code}

