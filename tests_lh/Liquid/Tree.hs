module Tree where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

data Tree v = Tree v | Leaf


{-@ sumPosTree :: t:Tree {y:Int | y >= 0} -> {x:Int | x >= 0} @-}
sumPosTree :: Tree Int -> Int
sumPosTree _ = sumTree

sumTree :: Int
sumTree = 0