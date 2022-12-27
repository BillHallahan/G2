{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}


module Combined (M, k) where

import Prelude hiding (map)

data X a = X a 
data M a = M (X a)

{-@ k :: M ({v:Int | v = 1}) @-}
k :: M Int
k = map cs 1

cs :: Int -> Int
cs p = p

map :: (a -> a) -> a -> M a
map f x = M ((\v -> X (f v)) x)