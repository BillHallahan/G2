module Cast1 where

import Data.Typeable

castInt :: Int -> Maybe Int
castInt = callInt

badCastInt :: Float -> Maybe Int
badCastInt = callInt

callInt :: Typeable a => a -> Maybe Int
callInt a = case cast a of
                Just x -> Just (x + 1)
                Nothing -> Nothing

castListInt :: [Int] -> Maybe [Int]
castListInt = callListInt

callListInt :: Typeable a => a -> Maybe [Int]
callListInt a = cast a

castMaybeInt :: Maybe Int -> Maybe (Maybe Int)
castMaybeInt = callMaybeInt

callMaybeInt :: Typeable a => a -> Maybe (Maybe Int)
callMaybeInt a = 
    case cast a :: Maybe (Maybe Int) of
        Just (Just x) -> Just . Just $ x + 1
        y -> y

castFunc :: Int
castFunc =
    case callFunc (\x -> x + (1 :: Int)) of
        Just f -> f 7
        Nothing -> 0

callFunc :: Typeable a => a -> Maybe (Int -> Int)
callFunc a =
    case cast a :: Maybe (Int -> Int) of
        Just f -> Just (\x -> f x * 2)
        Nothing -> Nothing

callTypeOf1 :: Maybe Int -> Maybe Int -> (Bool, Bool)
callTypeOf1 x y = (x == y, typeOf x == typeOf y)

callTypeOf2 :: (Int -> Int) -> (Int -> Int) -> (Bool, Bool)
callTypeOf2 f g = (f 0 == g 0, typeOf f == typeOf g)

callTypeOf3 :: Int -> Float -> Bool
callTypeOf3 x y = typeOf x == typeOf y