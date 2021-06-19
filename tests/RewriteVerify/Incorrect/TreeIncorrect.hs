{-# LANGUAGE BangPatterns #-}

module TreeIncorrect where

data SimpleTree = SLeaf
                | SBranch SimpleTree SimpleTree

treeSize :: SimpleTree -> Int
treeSize SLeaf = 1
treeSize (SBranch st1 st2) = 1 + (treeSize st1) + (treeSize st2)

treeForce :: SimpleTree -> SimpleTree
treeForce SLeaf = SLeaf
treeForce (SBranch !st1 !st2) = SBranch (treeForce st1) (treeForce st2)

data BTree t = BLeaf
             | BBranch t (BTree t) (BTree t)

bmap :: (a -> b) -> BTree a -> BTree b
bmap _ BLeaf = BLeaf
bmap f (BBranch e t1 t2) = BBranch (f e) (bmap f t1) (bmap f t2)

p1 :: Int -> Int
p1 = (+ 1)

t2 :: Int -> Int
t2 = (* 2)

m1 :: Int -> Int
m1 x = x - 1

mod10 :: Int -> Int
mod10 x = mod x 10

bst :: BTree Int -> Bool
bst BLeaf = True
bst (BBranch i t0@(BBranch j _ _) BLeaf) = i >= j && bst t0
bst (BBranch i BLeaf t0@(BBranch k _ _)) = i <= k && bst t0
bst (BBranch i t0@(BBranch j _ _) t1@(BBranch k _ _)) =
  i >= j && i <= k && bst t0 && bst t1

-- TODO Z3 exhausted on bstMod; is it really invalid?
{-# RULES
"badSize" forall st1 st2 . treeSize (SBranch st1 st2) = 1 + (2 * treeSize st1)
"treeMapBackward" forall bt . bmap p1 (bmap t2 bt) = bmap (t2 . p1) bt
"bstMod" forall bt . bst (bmap mod10 bt) = bst bt
  #-}

-- TODO I get SAT for this but UNSAT for forceDoesNothing
{-# RULES
"treeForceNothing" forall st . treeForce st = st
  #-}
