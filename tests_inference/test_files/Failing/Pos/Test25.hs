{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (k) where

import Prelude hiding (map)

data M a = M a

{-@ k :: M ({ b:Bool | b }) @-}
k   :: M Bool
k = map cs (True, True)

cs :: Bool -> Bool
cs p = p

map :: (a -> a) -> (a, a) -> M a
map f t = M ((\(k, v) -> f v) t)