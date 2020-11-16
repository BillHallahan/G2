module Combined ( C
                , k
                , cs) where

import Prelude hiding (map)

data C a = C a

{-@ k :: C ({v:Int | v = 0}) @-}
k :: C Int
k = map cs (C 0)

map :: (a -> b) -> C a -> C b
map f (C x) = C (f x)

cs :: Int -> Int
cs p = p
