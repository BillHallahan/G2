{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List
                , prop_concat) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

infixr 9 :+:

concat    :: List (List a) -> List a

{-@ type TRUE = {v:Bool | v} @-}

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}


{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

l3     = 3 :+: 2 :+: 1 :+: l0

{-@ l0 :: { r:List Int | size r == 0 } @-}
l0     = Emp :: List Int

{-@ measure sizeXs          :: List (List a) -> Int
        sizeXs (Emp)            = 0
        sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}

length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys

{-@ prop_concat :: TRUE @-}
prop_concat = length (concat xss) == 3
  where
    xss     = l0 :+: l3 :+: Emp