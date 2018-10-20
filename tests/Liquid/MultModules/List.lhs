\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module List where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

z   :: List Double -> List Double -> List Double

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)


{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

{-@ z :: xs:List Double -> ListX Double xs -> ListX Double xs @-}
z Emp Emp               = Emp
z (x :+: xs) (y :+: ys) = (x + y) :+: z xs ys
z _ _                   = die  "Bad call to zipWith"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
\end{code}
