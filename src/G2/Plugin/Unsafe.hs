{-# LANGUAGE BangPatterns, MagicHash, RankNTypes, ScopedTypeVariables, TypeApplications #-}

module G2.Plugin.Unsafe ( assume
                        , exists
                        , exists2
                        , exists3
                        , exists4
                        , exists5) where

import G2.Plugin.Prim

-- | Assume that a condition is true
assume :: Bool -- ^ Condition to assume
       -> a -- ^ 
       -> a
assume _ x = x
{-# NOINLINE assume #-}

exists :: forall a . (a -> Bool) -> a
exists p = let !x = pSymGen# @a in assume (p x) x

exists2 :: forall a b . (a -> b -> Bool) -> (a, b)
exists2 p = let !x = pSymGen# @a 
                !y = pSymGen# @b in assume (p x y) (x, y)

exists3 :: forall a b c . (a -> b -> c -> Bool) -> (a, b, c)
exists3 p = let !x = pSymGen# @a 
                !y = pSymGen# @b
                !z = pSymGen# @c in assume (p x y z) (x, y, z)

exists4 :: forall a b c d . (a -> b -> c -> d -> Bool) -> (a, b, c, d)
exists4 p = let !w = pSymGen# @a 
                !x = pSymGen# @b
                !y = pSymGen# @c
                !z = pSymGen# @d in assume (p w x y z) (w, x, y, z)

exists5 :: forall a b c d e . (a -> b -> c -> d -> e -> Bool) -> (a, b, c, d, e)
exists5 p = let !v = pSymGen# @a 
                !w = pSymGen# @b
                !x = pSymGen# @c
                !y = pSymGen# @d
                !z = pSymGen# @e in assume (p v w x y z) (v, w, x, y, z)
