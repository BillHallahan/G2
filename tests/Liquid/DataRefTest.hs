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