{-# LANGUAGE RankNTypes #-}

module RankN where

identity :: (forall a. a -> a) -> Int
identity f = f 1

twoArgs :: (forall a. a -> a -> a) -> Int 
twoArgs f = f 1 2

calledInMaybe :: (forall a. a -> a) -> Maybe Int
calledInMaybe f = Just (f 2)

twoTVs :: (forall a b. b-> a -> b -> b) -> Bool
twoTVs f = f True 25 False

twoTVs_ :: (forall a b. b -> a -> b -> b) -> (Bool, Float)
twoTVs_ f = (f True 25 False, f 40.0 True 39.9)

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

funcArg :: (forall a. (a -> a) -> a -> a) -> Int 
funcArg f = f (\x -> x + 1) 2


funcArg2 :: (forall a. (a -> a) -> a -> a) -> Int 
funcArg2 f = f (\x -> x) 2

-- FAILING after 170
funcArgTwice :: (forall a. (a -> a) -> a -> a) -> (Int, Int)
funcArgTwice f = (f (\x -> x) 2,  f (\x -> x) 3)

funcArg4 :: (forall a. (a -> a) -> a) -> Int 
funcArg4 f = f (\_ -> 1)

funcArg4Tup :: (forall a. (a -> a) -> a -> a) -> (Int, Int)
funcArg4Tup f = (f (\_ -> 1) 2 , f (\x->x) 2)

funcArg3 :: (forall a. (a -> a -> a) -> a -> a) -> Int 
funcArg3 f = f (\x y -> x + y) 1

funcArgSol = (\fs'2 -> (\fs -> let
      fs'5 = fs'2 fs in case fs'5 of
      _ -> let
            fs'6 = fs'2 (let
                  fs'3 = fs'2 fs in case fs'3 of
                  _ -> fs'3) in case fs'6 of
            _ -> fs'5))

funcArgSol_ = (\fs'2 -> (\fs -> fs))

funcArg2TVs :: (forall a b. (b -> a) -> b -> a) -> Bool  
funcArg2TVs f = f (\x -> case x of 
                        2 -> True
                        _ -> False 
                    ) 2

funcArg2TVsFailing :: (forall a b. (b -> a) -> b -> a) -> Int 
funcArg2TVsFailing f = f (\x -> case x of 
                            _ -> 5
                            ) 2

funcArgBothAsFailing :: (forall a. (a -> a) -> a -> a) -> Int 
funcArgBothAsFailing f = f (\x -> 1) 2

funcArgNeedsUndef :: (forall a b. (b -> a) -> b -> a) -> Int
funcArgNeedsUndef g = g (\x -> 1) (let y = y in y)

funcArgNeedsUndef2 :: (forall a b. (b -> a) -> a) -> Int
funcArgNeedsUndef2 g = g (\x -> 1)

funcArgNeedsEval :: (forall a . (a -> a) -> a) -> Int
funcArgNeedsEval g = g (\x -> x)


-- TESTING
funcNeedsUndefTuple :: (forall a b. (b -> a) -> b -> a) -> (Int, Int)
funcNeedsUndefTuple f = (f (\x -> 1) (let y = y in y), f (\x -> x) 2)


--- currently working out a possible error invovling executing PM funcs with function arguments multiple times
--- probably a problem with deepRenaming and newBindings
--- also considering FA application store to prevent branching, but need to worry about scope as well
--- merged master