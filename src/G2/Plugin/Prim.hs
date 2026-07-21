{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}

module G2.Plugin.Prim where

import GHC.Exts

{-# NOINLINE pSmtLen# #-}
pSmtLen# :: [a] -> Int#
pSmtLen# _ = 0#

{-# NOINLINE pSmtAppend# #-}
pSmtAppend# :: [a] -> [a] -> [a]
pSmtAppend# xs _ = xs

{-# NOINLINE pIsSMTRep# #-}
pIsSMTRep# :: [a] -> Bool
pIsSMTRep# _ = True

