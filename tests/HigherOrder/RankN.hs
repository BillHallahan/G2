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

argFromMaybe :: (forall a. (Maybe a) -> a) -> Int 
argFromMaybe f = f (Just 2)

twoFunctions :: (forall a. a -> a -> a) -> (forall a. a -> a -> a) -> (Int, Int)
twoFunctions f g = (f 1 2, g 3 4)
