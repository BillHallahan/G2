module DataRefTest where

import Prelude hiding (Maybe (..), Either (..))

data Maybe a = Just a | Nothing
data Either a b = Left a | Right b

{-@ addMaybe :: Maybe Int -> y:Int -> Maybe {z:Int | z > y} @-}
addMaybe :: Maybe Int -> Int -> Maybe Int
addMaybe (Just x) y = Just (x + y)
addMaybe _ _ = Nothing

{-@ addMaybe2 :: Maybe {x:Int | x >= 0 } -> {y:Int | y >= 0} -> Maybe {z:Int | z > y} @-}
addMaybe2 :: Maybe Int -> Int -> Maybe Int
addMaybe2 (Just x) y = Just (x + y)
addMaybe2 _ _ = Nothing

{-@ measure isJust @-} 
isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

{-@ measure isNothing @-} 
isNothing :: Maybe a -> Bool
isNothing Nothing = True
isNothing _ = False

getLeftInts :: Either Int Int -> Int
getLeftInts = getLeft

getLeft :: Either a b -> a
getLeft (Left x) = x
getLeft _ = die 0

{-@ sumSameInts :: e:Either Int Int -> {e2:Either Int Int | isLeft e => isLeft e2} -> Either Int Int @-} 
sumSameInts :: Either Int Int -> Either Int Int -> Either Int Int
sumSameInts = sumSame

{-@ sumSame :: (Num a, Num b) => e:Either a b -> {e2:Either a b | isLeft e => isLeft e2} -> Either a b @-} 
sumSame :: (Num a, Num b) => Either a b -> Either a b -> Either a b
sumSame (Left x) (Left y) = Left (x + y)
sumSame (Right x) (Right y) = Right (x + y)
sumSame _ _ = die 0 

{-@ measure isLeft @-}
isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

{-@ measure isRight @-}
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

{-@ die :: {x:Int | false} -> a @-}
die :: Int -> a
die x = error "die"

{-@ sub1 :: Num a => a -> {y:a | y >= 0} @-}
sub1 :: Num a => a -> a
sub1 x = x - 1

{-@ id2 :: Num a => x:a -> {y:a | y >= 0} @-}
id2 :: Num a => a -> a
id2 z = z

{-@ const4 :: Num a => {y:a | y >= 0} @-}
const4 :: Num a => a
const4 = -4

{-@ check :: (Num a, Num b) => x:a -> y:b -> {y:b | y <= x || y > x} @-}
check :: (Num a, Num b) => a -> b -> b
check x y  = y

-- 800
fI :: Num a => a
fI = -1