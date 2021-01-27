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
                , prop_replicate) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

replicate :: Int -> a -> List a
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

(a) Computing the Length of a List
----------------------------------

Write down a *refined* type for `length`:

\begin{code}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs
\end{code}

\begin{code}
empty = Emp
\end{code}

(c) Replicating Values
----------------------

Fill in the code, and update the refinement type specification
for `replicate n x` which should return a `List` `n` copies of
the value `x`:

\begin{code}
replicate n x
  | n == 0    = empty
  | otherwise = x :+: replicate (n - 1) x
\end{code}

When you are done, the following assertion should be verified by LH.

\begin{code}
{-@ prop_replicate :: Nat -> a -> TRUE @-}
prop_replicate n x = lAssert (n == length (replicate n x))
\end{code}
