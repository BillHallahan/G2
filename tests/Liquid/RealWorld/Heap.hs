{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff" @-}
{-# LANGUAGE LambdaCase #-}
module Heap where
import           Data.Maybe (fromMaybe)

-- Implementation inspired by http://typeocaml.com/2015/03/12/heap-leftist-tree/

type Depth = Int

data Heap a = Leaf | Branch !a (Heap a) (Heap a)

-- TODO: Possible to avoid record syntax?
-- TODO: Possible to avoid data refinement altogether, relying on smart constructors?
{-@ data Heap a = Leaf | Branch {elt :: a, l :: OLHeap a elt, r :: OLHeap a elt} @-}

-- TODO: How to write `OHeap` and `LHeap` so that they compose?
{-@ type OHeap a X = Heap {v:a | v < X} @-}
{-@ type LHeap a = {v:Heap a | Prop (isLeftist v)} @-}
{-@ type OLHeap a X = {v:OHeap a X | Prop (isLeftist v)} @-}

{-@ measure isLeftist :: Heap a -> Bool
isLeftist = \case
  Leaf -> True
  Branch _ l r -> rank l >= rank r @-}

{-@ measure rank :: Heap a -> Int @-}
rank = \case
  Leaf -> 0
  Branch _ l r -> min (rank l) (rank r)

-- TODO: When to use this style of invariant, which exposes some property?
{-@ type RankedHeap a X = {v:Heap a | rank v == X} @-}

{-@ singleton :: a -> RankedHeap a 1 @-}
singleton x = Branch x Leaf Leaf

-- TODO: Shouldn't LH figure out that a `Leaf` has rank 0?
{-@ empty :: RankedHeap a 0 @-}
empty = Leaf

swap (x,y) = (y,x)

splitMin :: Ord t => Heap t -> Maybe (t, Heap t)
splitMin = \case
  Leaf -> Nothing
  Branch x l r -> Just (x, merge l r)

getMin :: Ord t => Heap t -> Maybe t
getMin = fmap fst . splitMin

deleteMin :: Ord t => Heap t -> Heap t
deleteMin = fromMaybe empty . fmap snd . splitMin

merge :: Ord t => Heap t -> Heap t -> Heap t
merge Leaf h = h
merge h Leaf = h
merge h1@(Branch x1 l r) h2@(Branch x2 _ _) =
  if x2 < x1 then merge h2 h1 else
    Branch x1 l' r'
  where
    merged = merge r h2
    (l', r') = (if rank l >= rank merged then id else swap)
      (l, merged)

insert x h = merge (singleton x) h