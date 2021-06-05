{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data R  = Emp | D
         deriving (Eq, Ord, Show)

{-@ measure size :: R -> Int
    size Emp = 0
    size D = 1
  @-}

{-@ invariant {v:R | 0 <= size v} @-}

data Assocs k a = Assocs a

{-@ f :: Assocs Int R -> {xs:R | 0 < size xs} @-}
f :: Assocs Int R -> R
f (Assocs m) = m
