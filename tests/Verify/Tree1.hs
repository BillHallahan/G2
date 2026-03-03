module Tree where

data Tree a = Branch (Tree a) a (Tree a) | Leaf

instance Eq a => Eq (Tree a) where
    Branch l1 x1 r1 == Branch l2 x2 r2 = l1 == l2 && x1 == x2 && r1 == r2
    Leaf == Leaf = True
    _ == _ = False

instance Functor Tree where
    fmap f (Branch l x r) = Branch (fmap f l) (f x) (fmap f r)
    fmap f Leaf = Leaf

fmapIdTree :: Eq a => Tree a -> Bool
fmapIdTree xs = fmap id xs == id xs

fmapCompositionTree :: Eq c => (b -> c) -> (a -> b) -> Tree a -> Bool
fmapCompositionTree f g xs = fmap (f . g) xs == (fmap f . fmap g) xs
