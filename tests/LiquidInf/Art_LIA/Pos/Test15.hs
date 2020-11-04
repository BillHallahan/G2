{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-} 

module Combined (C, f) where

data C a = Emp | C a

{-@ measure isC :: C a -> Int
    isC Emp = 0
    isC (C x) = 1
  @-}

{-@ invariant {v:C a | 0 <= isC v} @-}
{-@ invariant {v:C a | isC v <= 1} @-}

{-@ f :: (k, ({ xs:C v | isC xs > 0 })) -> v @-}
f :: (k, C v) -> v
f m = g m

g :: (k, C v) -> v
g (k, C x) = x
g _ = die ""

{-@ die :: {v:String | false} -> a @-}
die = error
