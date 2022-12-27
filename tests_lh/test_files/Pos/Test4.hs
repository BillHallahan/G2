-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where


data C a = C a
         deriving (Eq, Ord, Show)

{-@ f :: C (C { x:Int | x >= 0 }) @-}
f :: C (C Int)
f = g 0

{-@ g  :: Int -> C (C Int) @-}
g :: Int -> C (C Int)
g _ = C (C 0)