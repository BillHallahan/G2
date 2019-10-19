module Tree where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

data Tree v = Tree (Tree v) v (Tree v)
            | Leaf

-- Has to synthesize and use:
-- {-@ measure treePos @-}
-- treePos :: Tree Int -> Bool
-- treePos (Tree t1 x t2) = x >= 0 && treePos t1 && treePos t2
-- treePos Leaf = True

{-@ sumPosTree :: t:Tree {y:Int | y >= 0} -> {x:Int | x >= 0} @-}
sumPosTree :: Tree Int -> Int
sumPosTree = sumTree

{-@ sumTree :: t:Tree Int -> Int @-}
sumTree :: Tree Int -> Int
sumTree (Tree t1 x t2) = x + sumTree t1 + sumTree t2
sumTree Leaf = 0