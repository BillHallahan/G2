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

polyFuncArgOneArgKind :: ((forall m. m Int -> m Int) -> Int) -> Int
polyFuncArgOneArgKind f = f (\x -> x)

polyFuncArgTwoArgKind :: ((forall m. m Int Bool -> m Int Bool) -> Int) -> Int
polyFuncArgTwoArgKind f = f (\x -> x)

polyFuncArgTwoKinds :: ((forall m a. m a -> m a) -> Int) -> Int
polyFuncArgTwoKinds f = f (\x -> x)

polyFuncArgThreeKinds :: ((forall m a b. m a b -> m a b) -> Int) -> Int
polyFuncArgThreeKinds f = f (\x -> x)

polyFuncArgHigherKind :: ((forall m. m Maybe -> m Maybe) -> Int) -> Int
polyFuncArgHigherKind f = f (\x -> x)

-- Tests application of polymorphic functions and instantiation of them. The function 
-- with type (forall a b. a -> b -> (Boxed a, b)) will be created as a symbolic 
-- argument and instantiated by polymorphic function inst-ing rules.
polyFuncArgWithPolyFuncArg :: ((forall a. (forall a b. a -> b -> (Boxed a, b)) -> a -> (Boxed a, a)) -> Int) -> Int
polyFuncArgWithPolyFuncArg g = g (\poly x -> poly x x)

-- For checking in logs that the (forall a. (forall b. a -> b -> (Boxed a, b)) argument 
-- is passed as a symbolic (forall b. Integer -> b -> (Boxed Integer, b)).
polyFuncArgWithPolyFuncArg2 :: ((forall a. (forall b. a -> b -> (Boxed a, b)) -> a -> (Boxed a, a)) -> Int) -> Int
polyFuncArgWithPolyFuncArg2 g = g (\poly x -> poly x x)

-- TODO: the following all have type variables bound to @Integer, different from above
--------- [Polymorphic functions with polymorphic function arguments] ---------

-- The polymorphic argument is floated out by PM-FLOAT-OUT and handled 
-- by SF-FUNC-FORALL. Not testing anything different from above.
forallWithPolyFuncArg :: (forall a. (forall b. b -> b) -> a -> a) -> Bool
forallWithPolyFuncArg f = f (\x -> x) True

-- In the following three functions, the function argument contains
-- tv's bound by the forall, so it cannot be floated out. PM-FUNC-FORALL will handle these cases.
forallWithPolyFuncArg2 :: (forall a. (forall b. a -> b -> b) -> a -> a) -> Bool
forallWithPolyFuncArg2 f = f (\x y -> y) True

forallWithPolyFuncArg3 :: (forall a. (forall b. a -> b -> a) -> a -> a) -> Bool
forallWithPolyFuncArg3 f = f (\x y -> x) True

forallWithPolyFuncArgSecond :: (forall a. a -> (forall b. a -> b -> a) -> a) -> Bool
forallWithPolyFuncArgSecond f = f True (\x y -> x)

forallWithPolyFuncArgBox :: (forall a. (forall b. b -> Boxed b) -> a -> Boxed a) -> Boxed Bool
forallWithPolyFuncArgBox f = f (\x -> Box x) True

-- TODO: test takes too long
-- Current rules will not find the simplest definition that applies the tuple-making 
-- function to the a and b arguments because:
--  1. The tuple-making function is floated out.
--  2. ADT return types are constructed from scratch whenever they are returned, so an 
--     existing (a, b) will not be used.
forallWithPolyFuncArgTup :: (forall a b. (forall c d. c -> d -> (c, d)) -> a -> b -> (a, b)) -> (Bool, Int)
forallWithPolyFuncArgTup f = f (\x y -> (x, y)) True 7
