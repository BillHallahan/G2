{-# LANGUAGE RankNTypes #-}

module RankN2 where

--------- [Identity functions] ---------
identityInTuple :: (forall a. a -> (a, a)) -> (forall a. a -> a) -> ((Int, Int), Int)
identityInTuple f g = (f 3, g 5)

intArg :: (forall a. a -> Int -> a) -> Int
intArg f = f 1 2

identityTwoTvs :: (forall b a c. a -> a) -> Int
identityTwoTvs f = f 1

--------- [ADT Arguments] ---------
data Tree a = Leaf a | Inter (Tree a) (Tree a) deriving (Eq, Show)
data Boxed a = Box a deriving (Eq, Show)

boxedArg :: (forall a. a -> Boxed a -> a) -> Int
boxedArg f = f 4 (Box 1)

treeArg :: (forall a. Tree a -> a) -> Int
treeArg f = f (Inter (Leaf 3) (Inter (Leaf 7) (Leaf 8)))

--------- [ADT Return Values] ---------
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

--------- [Function arguments] ---------
funcArg :: (forall a. (a -> a) -> a -> a) -> Int
funcArg f = f (\x -> x + 1) 3

funcArgBoxedArg :: (forall a. (Boxed a -> a) -> Boxed a -> a) -> Int
funcArgBoxedArg f = f (\(Box x) -> x) (Box 3)

funcArgBoxedLitArg :: (forall a. a -> (Boxed Int -> a -> a) -> a) -> Bool
funcArgBoxedLitArg f = f False (\(Box i) x -> x)

--------- [Multiple function applications] ---------
twoApplicationsNeeded :: (forall a b c. (a -> b) -> (b -> c) -> a -> c) -> Int
twoApplicationsNeeded f = f (\x -> x) (\x -> x) 7

--------- [Typeclasses - not handled yet] ---------
useTypeClass :: (forall a. (Num a) => a -> a) -> Int
useTypeClass f = f 8

funcArgNum :: ((forall b. (Num b) => b -> b) -> Int) -> Int
funcArgNum f = f (\x -> x + 1)

--------- [Functions with polymorphic function arguments] ---------
polyFuncArg :: ((forall a. a -> a) -> Int) -> Int
polyFuncArg f = f (\x -> x)

polyFuncArgTwoTVs :: ((forall a b. a -> b -> (a, b)) -> Int) -> Int
polyFuncArgTwoTVs f = f (\x y -> (x, y))

polyFuncArgADT :: ((forall a. (Boxed (Boxed a)) -> a) -> Int) -> Int
polyFuncArgADT f = f (\(Box (Box x)) -> x)

polyFuncArgWithFuncArg :: ((forall a. (a -> a) -> a -> a) -> Int) -> Int
polyFuncArgWithFuncArg g = g (\f x -> f x)

polyFuncArgWithPolyFuncArg :: ((forall a. (forall a b. a -> b -> (Boxed a, b)) -> a -> (Boxed a, a)) -> Int) -> Int
polyFuncArgWithPolyFuncArg g = g (\poly x -> poly x x)

-- For checking in logs that the (forall a. (forall b. a -> b -> (Boxed a, b)) argument 
-- is passed as a symbolic (forall b. Integer -> b -> (Boxed Integer, b)).
polyFuncArgWithPolyFuncArg2 :: ((forall a. (forall b. a -> b -> (Boxed a, b)) -> a -> (Boxed a, a)) -> Int) -> Int
polyFuncArgWithPolyFuncArg2 g = g (\poly x -> poly x x)

--------- [Polymorphic functions with polymorphic function arguments] ---------
forallWithPolyFuncArg :: (forall a. (forall b. b -> b) -> a -> a) -> Bool
forallWithPolyFuncArg f = f (\x -> x) True

-- TODO: The function argument contains tv's bound by the forall, 
-- so it cannot be floated out. Current rules do not handle.
forallWithPolyFuncArg2 :: (forall a. (forall b. a -> b -> b) -> a -> a) -> Bool
forallWithPolyFuncArg2 f = f (\x y -> y) True

forallWithPolyFuncArgBox :: (forall a. (forall b. b -> Boxed b) -> a -> Boxed a) -> Boxed Bool
forallWithPolyFuncArgBox f = f (\x -> Box x) True

-- Current rules will not find the simplest definition that applies the tuple-making 
-- function to the a and b arguments because:
--  1. The tuple-making function is floated out.
--  2. ADT return types are constructed from scratch whenever they are returned, so an 
--     existing (a, b) will not be used.
forallWithPolyFuncArgTup :: (forall a b. (forall c d. c -> d -> (c, d)) -> a -> b -> (a, b)) -> (Bool, Int)
forallWithPolyFuncArgTup f = f (\x y -> (x, y)) True 7