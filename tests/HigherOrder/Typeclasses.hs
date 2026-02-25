{-# LANGUAGE RankNTypes #-}

class MyTC a where
    equal :: a -> a -> Bool
    all_true :: a -> a -> Bool


data MyDual = Foo | Bar deriving (Show)

instance MyTC MyDual where
    equal Foo Foo = True
    equal Bar Bar = True
    equal _ _ = False
    all_true _ _ = True

instance Eq MyDual where
    Foo == Foo = True
    Bar == Bar = True
    _ == _ = False

tcFunction :: (forall a. (MyTC a) => a -> a -> Bool) -> Bool
tcFunction f = f Foo Foo

tcFunction2 :: (forall a. (Eq a) => a -> a -> Bool) -> Bool
tcFunction2 f = f Foo Foo

tcFunction3 :: (forall a. (Num a) => a -> a) -> Int
tcFunction3 f = f 4