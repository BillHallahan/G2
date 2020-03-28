-- cmd_line = (--no-keep-quals)

module Combined () where

import Prelude hiding (foldr, map, zipWith, repeat)

data List a = D a

{-@ measure size :: List a -> Int
    size (D x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

map :: (a -> b) -> List a -> List b
map f (D x) = D (f x)

mapReduce :: List Int -> List Int
mapReduce xs = map (\_ -> 1) xs

{-@ f :: List Int -> List {v:Int | 0 <= v } @-}
f :: List Int -> List Int
f ps = mapReduce ps