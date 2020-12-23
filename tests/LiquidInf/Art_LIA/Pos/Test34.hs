{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List
                , f) where

import Prelude hiding (id)

data List a = Emp
            | C a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size :: List a -> Int
    size (Emp) = 0
    size (C x xs) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}
{-@ invariant {v:List a | size v <= 1} @-}

f :: List (k, v) -> [List v]
f xs = g xs

g    :: List (k, v) -> [List v]
g Emp = []
g (C (_, v) xs) = add v (g xs)

add v m = id Emp:m

call :: k -> List k
call k = id Emp
 
id :: List a -> List a
id xs = xs