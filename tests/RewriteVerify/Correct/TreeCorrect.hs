module TreeCorrect where

data SimpleTree = SLeaf
                | SBranch SimpleTree SimpleTree

treeSize :: SimpleTree -> Int
treeSize SLeaf = 1
treeSize (SBranch st1 st2) = 1 + (treeSize st1) + (treeSize st2)

data BTree t = BLeaf
             | BBranch t (BTree t) (BTree t)

bmap :: (a -> b) -> BTree a -> BTree b
bmap _ BLeaf = BLeaf
bmap f (BBranch e t1 t2) = BBranch (f e) (bmap f t1) (bmap f t2)

p1 :: Int -> Int
p1 = (+ 1)

t2 :: Int -> Int
t2 = (* 2)

bst :: BTree Int -> Bool
bst BLeaf = True
bst (BBranch i t0@(BBranch j _ _) BLeaf) = i >= j && bst t0
bst (BBranch i BLeaf t0@(BBranch k _ _)) = i <= k && bst t0
bst (BBranch i t0@(BBranch j _ _) t1@(BBranch k _ _)) =
  i >= j && i <= k && bst t0 && bst t1

{-# RULES
"doubleTree" forall st . treeSize (SBranch st st) = 1 + (2 * treeSize st)
"doubleMapTree" forall bt . bmap p1 (bmap t2 bt) = bmap (p1 . t2) bt
  #-}

-- these two rules take a long time to verify, but it does succeed
{-# RULES
"bstPlus" forall bt . bst (bmap p1 bt) = bst bt
"bstTimes" forall bt . bst (bmap t2 bt) = bst bt
  #-}
