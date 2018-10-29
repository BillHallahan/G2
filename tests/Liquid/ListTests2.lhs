Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module List where

import Prelude hiding (length)

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ length :: x:List a -> {v:Int | v = len(x)}@-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length l0 == 0)

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
\end{code}
