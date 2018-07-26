{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module L where

import Prelude hiding (foldr)

data L a = E
            | (:+:) a (L a)
            | (+:+) (L a) (L a)

{-@ measure s      :: L a -> Int
    s (E)        = 0
    s ((:+:) x xs) = 1
  @-}

(+:+) :: (L a) -> L a -> L a
(+:+) (x:+:E) ys = x :+: ys
(+:+) _ ys = ys

{-@ f :: L (L Int) -> {l:L Int | s l == 0} @-}
f :: L (L Int) -> L Int
f  E        = E
f  (x :+: xs) = x +:+ E

