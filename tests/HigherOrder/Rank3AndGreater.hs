{-# LANGUAGE RankNTypes #-}

data Boxed a = Box a deriving (Eq, Show)

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

forallWithPolyFuncArg3 :: (forall a. (forall b. a -> b -> a) -> a -> a) -> Bool
forallWithPolyFuncArg3 f = f (\x y -> x) True

forallWithPolyFuncArgBox :: (forall a. (forall b. b -> Boxed b) -> a -> Boxed a) -> Boxed Bool
forallWithPolyFuncArgBox f = f (\x -> Box x) True

-- Current rules will not find the simplest definition that applies the tuple-making 
-- function to the a and b arguments because:
--  1. The tuple-making function is floated out.
--  2. ADT return types are constructed from scratch whenever they are returned, so an 
--     existing (a, b) will not be used.
forallWithPolyFuncArgTup :: (forall a b. (forall c d. c -> d -> (c, d)) -> a -> b -> (a, b)) -> (Bool, Int)
forallWithPolyFuncArgTup f = f (\x y -> (x, y)) True 7