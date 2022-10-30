Lists
=====

\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module ZipWith2 ( List
                , foldr
                , zipWith
                ) where

import Prelude hiding ( foldr, zipWith)

infixr 9 :+:


data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

type Point   = List Double

{-@ distance :: Point -> Point -> Point @-}
distance :: Point -> Point -> Point
distance px py = zipWith px py

{-@ zipWith :: xs:List Double -> List a -> ListX Double xs @-}
zipWith   :: List Double -> List a -> List Double
zipWith Emp Emp               = Emp
zipWith (x :+: xs) (y :+: ys) = x :+: zipWith xs ys
zipWith _          _          = die  "Bad call to zipWith"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

\end{code}
