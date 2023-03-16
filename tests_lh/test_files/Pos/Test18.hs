{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (C, f) where

data C a =  C

{-@ measure c :: C (C a) -> Int
        c C = 1
  @-}
    
{-@ f :: k:Nat -> C (C a) -> Maybe {v:Int | v = k} @-}
f   :: Int -> C (C a) -> Maybe Int
f k = g (h k)

g :: v -> C a -> Maybe v
g _ _ = Nothing

h :: Int -> Int
h x = x
