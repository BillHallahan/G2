{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (EC, f) where

data EC a = E | C

{-@ measure size :: EC a -> Bool
    size E = True
    size C = False
  @-}

s :: EC a -> Bool
s E = True
s C = False

{-@ f :: {v:Bool | v} @-}
f :: Bool
f = s E