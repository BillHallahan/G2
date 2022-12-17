Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module List where

import Prelude hiding (length, map, replicate)

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ length :: x: (List a) -> {v:Int | v = (size x)} @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
\end{code}

\begin{code}
{-@ map :: (a -> b) -> List a -> List b @-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))
\end{code}

\begin{code}
{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ replicate :: n:Int -> a -> ListN a n @-}
replicate :: Int -> a -> List a
replicate 0 x = Emp
replicate n x = x :+: (replicate n x)
\end{code}

\begin{code}
length2            :: List a -> Int
length2 Emp        = 0
length2 (x :+: xs) = 1 + length2 xs

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length2 l3 == 3)

{-@ l3 :: ListN Int 3 @-}
l3     = 3 :+: l2

{-@ l2 :: ListN Int 2 @-}
l2     = 2 :+: l1

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: l0

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int
\end{code}
