module MapRules where

import Prelude hiding (map)

map :: (a -> b) -> [a] -> [b]
map f (x:xs) = f x:map f xs
map _ [] = []
{-# NOINLINE [0] map #-}

{-# RULES
 "map/map"   forall f g xs . map f (map g xs) = map (f . g) xs
  #-}