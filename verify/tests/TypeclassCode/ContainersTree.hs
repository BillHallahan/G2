module TypeclassCode.ContainersTree where

-- | Non-empty, possibly infinite, multi-way trees; also known as /rose trees/.
data Tree a = Node {
        rootLabel :: a,         -- ^ label value
        subForest :: [Tree a]   -- ^ zero or more child trees
    }
    deriving Eq

-- | This type synonym exists primarily for historical
-- reasons.
type Forest a = [Tree a]

instance Functor Tree where
    fmap = fmapTree
    x <$ Node _ ts = Node x (map (x <$) ts)

fmapTree :: (a -> b) -> Tree a -> Tree b
fmapTree f (Node x ts) = Node (f x) (map (fmapTree f) ts)

fmapIdTree :: Eq a => Tree a -> Bool
fmapIdTree xs = fmap id xs == id xs