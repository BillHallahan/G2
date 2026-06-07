{-# LANGUAGE RankNTypes #-}

data MyADT = Foo | Bar deriving (Show)
instance Eq MyADT where
    Foo == Foo = True
    Bar == Bar = True
    _ == _ = False

-- TODO[Jacob]: Generated instances are not guaranteed to follow any type class law, such as one that requires 'all_true _ _ = False'.
class MyTC a where
    equal :: a -> a -> Bool
    all_true :: a -> a -> Bool

instance MyTC MyADT where
    equal Foo Foo = True
    equal Bar Bar = True
    equal _ _ = False
    all_true _ _ = True

class SingleMethod a where
    m1 :: a -> a

-- non-generated instance currently required to add SingleMethod to the typeclass struct, will fix
instance SingleMethod Bool where
    m1 True = False
    m1 False = True

-- TODO[Jacob]: unsure about handling of this sort of declaration
{- 
    instance (MyTC a) => (MyTC [a]) where
-}

-- TODO[Jacob]: Might not be handled when MyTC is a single method class.

--- [Instantiating a symbolic function with a type class constraint] ---
-- TODO[Jacob]: When inst'd def applies FA all_true, the arguments don't need to be evaluated, so left undefined. Causes source error.
tcFuncInstUserClassUserType :: (forall a. (MyTC a) => a -> a -> Bool) -> Int
tcFuncInstUserClassUserType f = case f Foo Foo of
                                    True -> 1
                                    False -> 2

tcFuncInstPrelClassUserType :: (forall a. (Eq a) => a -> a -> Bool) -> Int
tcFuncInstPrelClassUserType f = case f Foo Foo of 
                                    True -> 1
                                    False -> 2

tcFuncInstPrelClassPrelType :: (forall a. (Num a) => a -> a) -> Int
tcFuncInstPrelClassPrelType f = f 4

-- TODO[Jacob]: other kinds 


--- [Instantiating a symbolic function which has a function with a type class constraint as an argument] ---
tcFuncArgPrelClass :: ((forall a. (Eq a) => a -> a -> Bool) -> Int) -> Int
tcFuncArgPrelClass f = f (\x y -> x == y)

tcFuncArgUserClass :: ((forall a. (MyTC a) => a -> a -> Bool) -> Int) -> Int
tcFuncArgUserClass f = f (\x y -> equal x y)

tcFuncArgTwoMethodsUsed :: ((forall a. (Num a) => a -> a) -> Int) -> Int
tcFuncArgTwoMethodsUsed f = f (\x -> x * x + x)

tcFuncArgSingleMethodClass :: ((forall a. (SingleMethod a) => a -> a) -> Int) -> Int
tcFuncArgSingleMethodClass f = f (\x -> m1 x)

-- TODO[Jacob]: other kinds 


--- [TODO] ---
-- TODO[Jacob]: This is halting early. Don't know why
tcFunctionArgTwice :: ((forall a. (Eq a) => a -> a -> Bool) -> Bool) -> (Bool, Bool)
tcFunctionArgTwice f = (f (\x y -> x /= y), f (\x y -> x == y))

{- tcFunctionArg3List :: ((forall a. (MyTC a) => [a] -> [a] -> Bool) -> Int) -> Int
tcFunctionArg3List f = f (\x y -> equal x y) -}

-- TODO[Jacob]: At 300 step limit, source error when (==) always returns true, so no Num instance made.
tcFuncArgTwoClasses :: ((forall a. (Num a, Eq a) => a -> Bool) -> Int) -> Int
tcFuncArgTwoClasses f = f (\x -> x + x == x * x)

-- TODO[Jacob]: allow generated instances to use default impls. Have saved and insert into newly added dicts, so only MIN methods need to be instantiated.

-- TODO[Jacob]: An instance for MyTC isn't inserted into the TC struct and no Haskell instance is made for it. source error
class MyTC a => SubTC a where
    equalS :: a -> a -> Bool
    all_trueS :: a -> a -> Bool
instance SubTC MyADT where
    equalS = equal
    all_trueS = all_true
tcFunctionArg7 :: ((forall a. (SubTC a) => a -> a -> Bool) -> Int) -> Int
tcFunctionArg7 f = f (\x y -> equalS x y)

-- TODO[Jacob]: Multi-parameter classes not yet handled. Execution will not progress (I believe)
{- tcFunctionArg5 :: ((forall a. (MyTC2 a Integer) => a -> a -> Bool) -> Int) -> Int
tcFunctionArg5 f = f (\x y -> m1 x 7) -}
