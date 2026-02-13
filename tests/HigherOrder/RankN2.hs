{-# LANGUAGE RankNTypes #-}

module RankN2 where

identity :: (forall a. a -> a) -> Int
identity f = f 1

identity_in_tuple :: (forall a. a -> (a, a)) -> (forall a. a -> a) -> ((Int, Int), Int)
identity_in_tuple f g = (f 3, g 5)

twoArgs :: (forall a. a -> a -> a) -> Int
twoArgs f = f 1 2

intArg :: (forall a. a -> Int -> a) -> Int
intArg f = f 1 2

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

data Tree a = Leaf a | Inter (Tree a) (Tree a)
data Boxed a = Box a


adt_arg :: (forall a. a -> Boxed a -> a) -> Int
adt_arg f = f 4 (Box 1)

adt_arg2 :: (forall a. Boxed a -> Boxed a -> a) -> Int
adt_arg2 f = f (Box 1) (Box 2)

adt_maybe :: (forall a. Maybe a -> a) -> Int 
adt_maybe f = f (Just 4)

adt_tree :: (forall a. Tree a -> a) -> Int
adt_tree f = f (Inter (Leaf 3) (Inter (Leaf 7) (Leaf 8)))

adt_ret :: (forall a. a -> Boxed a) -> Boxed Int
adt_ret f = f 3

ret_tree :: (forall a. a -> a -> Tree a) -> Tree Int
ret_tree f = f 5 7

ret_list :: (forall a. a -> a -> [a]) -> [Int]
ret_list f = f 4 5

func_arg :: (forall a. (a -> a) -> a -> a) -> Int
func_arg f = f (\x -> x + 1) 3

func_arg_adt :: (forall a. (Boxed a -> a) -> Boxed a -> a) -> Int
func_arg_adt f = f (\(Box x) -> x) (Box 3)