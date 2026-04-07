-- From: https://mail.haskell.org/pipermail/beginners/2010-March/003857.html

module TypeclassCode.Tree where

data Tree a = Node (Tree a) a (Tree a) | Leaf deriving Show

instance Eq a => Eq (Tree a) where
    Node l1 x1 r1 == Node l2 x2 r2 = l1 == l2 && x1 == x2 && r1 == r2
    Leaf == Leaf = True
    _ == _ = False

instance Functor Tree where
    fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)
    fmap f Leaf = Leaf

instance Applicative Tree where
    pure x = let t = Node t x t in t
    
    Leaf <*> _ = Leaf
    _ <*> Leaf = Leaf
    Node l1 f1 r1 <*> Node l2 x2 r2 = Node (l1 <*> l2) (f1 x2) (r1 <*> r2)
  