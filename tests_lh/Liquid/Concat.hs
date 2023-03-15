{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module List ( List
            , concat
            ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

concat    :: List (List Int) -> List Int

{-@ type TRUE = {v:Bool | v} @-}

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
    size ((:+:) x xs) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ l0 :: List Int @-}
l0 :: List Int
l0     = Emp

{-@ concat :: x:List (List Int) -> v:List Int @-}
concat Emp = Emp
concat (xs :+: _) = append xs

{-@ append :: y:List Int -> z:List Int @-}
append :: List Int -> List Int
append Emp = Emp
append ys = ys

{-@ prop_concat :: TRUE @-}
prop_concat = concat xss == Emp
  where
    xss     = l0 :+: Emp