{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-} 

module Replicate where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

add       :: a -> List a -> List a

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs

{-@ replicate :: n:Nat -> a -> {l: (List a) | n = (size l)} @-}
replicate :: Int -> a -> List a
replicate n x = foldl (\acc _ -> x :+: acc) Emp [1..n]

{-@ r :: a -> {l: (List a) | 1 = (size l)} @-}
r :: a -> List a
r x = foldl (\acc _ -> x :+: acc) Emp [1]

