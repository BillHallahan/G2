{-# LANGUAGE RankNTypes #-}

module RankN2 where

-- Identity functions
identityInTuple :: (forall a. a -> (a, a)) -> (forall a. a -> a) -> ((Int, Int), Int)
identityInTuple f g = (f 3, g 5)

intArg :: (forall a. a -> Int -> a) -> Int
intArg f = f 1 2

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

-- ADT arguments
data Tree a = Leaf a | Inter (Tree a) (Tree a) deriving (Eq, Show)
data Boxed a = Box a deriving (Eq, Show)

boxedArg :: (forall a. a -> Boxed a -> a) -> Int
boxedArg f = f 4 (Box 1)

treeArg :: (forall a. Tree a -> a) -> Int
treeArg f = f (Inter (Leaf 3) (Inter (Leaf 7) (Leaf 8)))

-- ADT return values
boxedRet :: (forall a. a -> Boxed a) -> Boxed Int
boxedRet f = f 3

treeRet :: (forall a. a -> a -> Tree a) -> Tree Int
treeRet f = f 5 7

treeRet2 :: (forall a b. a -> b -> (Boxed Int, (Boxed (Boxed b), Boxed (Boxed (Boxed a))))) -> (Boxed Int, (Boxed (Boxed Bool), Boxed (Boxed (Boxed Int))))
treeRet2 f = f 5 False

listRet :: (forall a. a -> a -> [a]) -> [Int]
listRet f = f 4 5

literalRet :: (forall a. Boxed a -> a -> Int) -> Int
literalRet f = case f (Box 5) 23 of 
                5 -> 10
                4 -> 8
                _ -> 3

literalAndBoxedRet :: (forall a. a -> (Boxed Int, Boxed a)) -> (Boxed Int, Boxed Bool)
literalAndBoxedRet f = f True

-- Function arguments
funcArg :: (forall a. (a -> a) -> a -> a) -> Int
funcArg f = f (\x -> x + 1) 3

funcArgBoxedArg :: (forall a. (Boxed a -> a) -> Boxed a -> a) -> Int
funcArgBoxedArg f = f (\(Box x) -> x) (Box 3)

funcArgBoxedLitArg :: (forall a. a -> (Boxed Int -> a -> a) -> a) -> Bool
funcArgBoxedLitArg f = f False (\(Box i) x -> x)

-- Composition required
twoApplicationsNeeded :: (forall a b c. (a -> b) -> (b -> c) -> a -> c) -> Int
twoApplicationsNeeded f = f (\x -> x) (\x -> x) 7