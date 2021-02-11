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
                , prop_zipWith) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

empty     :: List a
zipWith   :: (a -> b -> c) -> List a -> List b -> List c
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

(a) Computing the Length of a List
----------------------------------

Write down a *refined* type for `length`:

\begin{code}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs
\end{code}

such that the following type checks:


(b) Constructing Lists
----------------------

Fill in the implementations of the following functions so that
LiquidHaskell verifies respect the given type signatures:

\begin{code}
empty = Emp
\end{code}


(f) ZipWith
-----------

Fix the specification of `zipWith` so that LH verifies:

+ The call to `die` inside `zipWith` and
+ The assert inside `prop_zipwith`.

\begin{code}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ prop_zipWith :: Num a => List a -> TRUE @-}
prop_zipWith xs = lAssert (length xs == length x2s)
  where
    x2s         = zipWith (+) xs xs
\end{code}

