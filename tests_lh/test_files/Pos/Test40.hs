
module Combined ( List
                , prop_size) where

import Prelude hiding (length)

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = error ""

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length l3 == 3)

l3     = 3 :+: 2 :+: 1 :+: Emp :: List Int
