module Length where

import Prelude hiding (length)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}


data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ length :: {v:List a | v /= Emp} -> Int @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1
