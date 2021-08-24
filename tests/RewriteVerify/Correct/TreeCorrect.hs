module TreeCorrect where

data SimpleTree = SLeaf
                | SBranch SimpleTree SimpleTree

treeSize :: SimpleTree -> Int
treeSize SLeaf = 1
treeSize (SBranch st1 st2) = (treeSize st1) + (treeSize st2)

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

leftmost :: BTree a -> [a]
leftmost BLeaf = []
leftmost (BBranch i l _) = i:(leftmost l)

rightmost :: BTree a -> [a]
rightmost BLeaf = []
rightmost (BBranch i _ r) = i:(rightmost r)

listMap :: (a -> b) -> [a] -> [b]
listMap _ [] = []
listMap f (h:t) = (f h):(listMap f t)

leftSize :: BTree a -> Int
leftSize BLeaf = 0
leftSize (BBranch _ l _) = 1 + leftSize l

rightSize :: BTree a -> Int
rightSize BLeaf = 0
rightSize (BBranch _ _ r) = 1 + rightSize r

listLength :: [a] -> Int
listLength [] = 0
listLength (_:t) = 1 + listLength t

posNegDistance :: BTree Int -> Int
posNegDistance BLeaf = 0
posNegDistance (BBranch i l r) =
  if i >= 0
  then 1 + posNegDistance l
  else 1 + posNegDistance r

posNegPath :: BTree Int -> [Int]
posNegPath BLeaf = []
posNegPath (BBranch i l r) =
  if i >= 0
  then i:(posNegPath l)
  else i:(posNegPath r)

{-# RULES
"doubleTree" forall st . treeSize (SBranch st st) = (2 * treeSize st)
"doubleMapTree" forall bt . bmap p1 (bmap t2 bt) = bmap (p1 . t2) bt
  #-}

{-# RULES
"bstPlus" forall bt . bst (bmap p1 bt) = bst bt
"bstTimes" forall bt . bst (bmap t2 bt) = bst bt
  #-}

{-# RULES
"leftMap" forall f bt . leftmost (bmap f bt) = listMap f (leftmost bt)
"leftLength" forall bt . listLength (leftmost bt) = leftSize bt
"rightLength" forall bt . listLength (rightmost bt) = rightSize bt
"pnd" forall bt . listLength (posNegPath bt) = posNegDistance bt
  #-}

-- TODO trying to isolate the problem
data TripleTree = TLeaf
                | TBranch TripleTree TripleTree TripleTree

leafCount :: TripleTree -> Int
leafCount TLeaf = 1
leafCount (TBranch l m r) = (leafCount l) + (leafCount m) + (leafCount r)

data ListTree = ListTree [ListTree]

listLeaves :: ListTree -> Int
listLeaves (ListTree []) = 1
listLeaves (ListTree l) = foldr (+) 0 (map listLeaves l)

{-# RULES
"tripleLeaf" forall tt . leafCount (TBranch tt tt tt) = 3 * leafCount tt
"listLeaf" forall lt . listLeaves (ListTree [lt]) = listLeaves lt
  #-}

slowFib :: Int -> Int
slowFib n | n < 0 = error "negative"
slowFib 0 = 0
slowFib 1 = 1
slowFib n = slowFib (n - 2) + slowFib (n - 1)

fastFibHelper :: [Int] -> Int -> [Int]
fastFibHelper acc n =
  if n < 0 then error "negative"
  else if n == 0 then acc
  else case acc of
    a:b:_ -> fastFibHelper ((a + b):acc) (n - 1)
    _ -> error "invalid input"

fastFib :: Int -> Int
fastFib n | n < 0 = error "negative"
fastFib 0 = 0
fastFib 1 = 1
fastFib n = case fastFibHelper [1,0] (n - 1) of
  h:_ -> h
  _ -> error "invalid input"

{-# RULES
"fib" slowFib = fastFib
  #-}
