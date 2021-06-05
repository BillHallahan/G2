{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined where

data C a = E | C

{-@ measure isC @-}
isC :: C a -> Int
isC E = 0
isC C = 1

{-@ invariant {v:C a | 0 <= isC v} @-}
{-@ invariant {v:C a | isC v <= 1} @-}

{-@ tc_num :: Num a => C a -> {v:Bool | v} @-}
tc_num x = isC x == isC y
  where
    y = f (+) x

f :: (a -> a -> a) -> C a -> C a
f _ E = E
f _ C = C