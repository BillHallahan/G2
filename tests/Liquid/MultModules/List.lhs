Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module List where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

import GHC.Generics

infixr 9 :+:

\end{code}
</div>


\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show, Generic)

z :: List Double -> List Double
z Emp       = Emp
z _         = die  "Bad call to zipWith"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
\end{code}
