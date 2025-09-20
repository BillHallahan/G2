module RankN where

identity :: (forall a. a -> a) -> Int
identity f = f 1

twoArgs :: (forall a. a -> a -> a) -> Int 
twoArgs f = f 1 2

calledInMaybe :: (forall a. a -> a) -> Maybe Int
calledInMaybe f = Just (f 2)

twoTVs :: (forall a b. b-> a -> b -> b) -> Bool
twoTVs f = f True 25 False

nested :: (forall a. a -> a -> a) -> Int
nested f =  f (f 1 2) 3

calledInTuple :: (forall a. a -> a -> a) -> (Int, Int)
calledInTuple f = (f 1 4, f 5 2)

intArg :: (forall a. a -> Int -> a) -> Bool
intArg f = f True 5

intArgCalledTwice :: (forall a. a -> a -> Int -> a) -> Int
intArgCalledTwice f = case f 2 7 9 of 
                2 -> f 5 6 10
                7 -> f 9 10 9
                _ -> 3

intArgCaseFourCalls :: (forall a. Int -> a -> a -> Int -> a) -> (Int, Int)
intArgCaseFourCalls f = (case f 2 10 11 12 of 
                    10 -> 9
                    _ -> case f 3 10 11 12 of
                        10 -> 7
                        _ -> case f 4 10 11 12  of
                            12 -> 6
                            _ -> 100 , f 4 10 11 12)

multiIntArgs :: (forall a. Int -> Int -> a -> a) -> Int
multiIntArgs f = f 2 3 4

fromMaybe :: (forall a. a -> (Maybe a) -> a) -> (Int, Int)
fromMaybe f = (f 1 (Just 2), f 3 Nothing)

-- | Checks that literals are not being generated in definition
-- TODO: maybe remove this test
fromMaybeInvalid :: (forall a. (Maybe a) -> a) -> Int 
fromMaybeInvalid f = f Nothing

fromTuples :: (forall a. (a, a) -> (a, a) -> a) -> Int 
fromTuples f = f (2, 3) (4, 5)

twoFunctions :: (forall a. a -> a -> a) -> (forall a. a -> a -> a) -> (Int, Int)
twoFunctions f g = (f 1 2, g 3 4)

partiallyApply :: (forall a. a -> a -> a) -> (Int, Int)
partiallyApply f = let pApp = f 1
                       pApp2 = f 3 in 
                        (pApp 2, pApp2 4)

twoTVsMultiCall :: (forall a b. a -> b -> b) -> Int 
twoTVsMultiCall f = case (f 1 2, f 3 4) of 
                        (2, 4) -> f 5 6