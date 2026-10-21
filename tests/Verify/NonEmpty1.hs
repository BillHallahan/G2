module NonEmpty1 where

data X = X

instance Eq X where
    _ == _ = True

prop1 :: NonEmpty -> Bool
prop1 xs = mapN id xs == xs

data NonEmpty = X :| [X]

instance Eq NonEmpty where
    x :| xs == y :| ys = xs == ys

infixr 5 :|

mapN :: (X -> X) -> NonEmpty -> NonEmpty
mapN f (a :| as) = f a :| fmap id as
