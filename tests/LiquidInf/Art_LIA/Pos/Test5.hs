-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where


data C a = C a
         deriving (Eq, Ord, Show)

{-@ f :: { x:Int | x >= 0 } @-}
f :: Int
f = g x

{-@ g  :: C (C Int) -> Int @-}
g :: C (C Int) -> Int
g (C (C x))
    | x >= 0 = 0
    | otherwise = -1

{-@ x :: C (C { y:Int | y >= 0}) @-}
x :: C (C Int)
x = C (C 0)
