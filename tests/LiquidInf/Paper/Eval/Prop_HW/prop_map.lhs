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
 

{-# LANGUAGE DeriveGeneric #-}

module Combined ( List
                , prop_map) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

infixr 9 :+:

map       :: (a -> b) -> List a -> List b
\end{code}
</div>

\begin{code}
{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

\end{code}

A Sized List Datatype
---------------------

Lets cook up our own `List` data type from scratch:

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
\end{code}

We can write a **measure** that logically represents
the *size*, i.e. number of elements of a `List`:

\begin{code}
{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListNE a = {v:List a | size v > 0} @-}
\end{code}

It will be helpful to have a few abbreviations. First,
lists whose size is equal to `N`

\begin{code}
{-@ type ListN a N  = {v:List a | size v = N} @-}
\end{code}
and then, lists whose size equals that of *another* list `Xs`:

\begin{code}
{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}
\end{code}


\begin{code}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs
\end{code}

(d) Map
-------

Fix the specification for `map` such that the assertion in `prop_map`
is verified by LH. (This will require you to first complete part (a) above.)

\begin{code}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))
\end{code}
