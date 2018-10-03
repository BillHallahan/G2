module FoldrTests where

{-@ LIQUID "--no-termination" @-}

import Prelude hiding (foldr)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ max2 :: List { x:Int | x > 0} -> { y:Int | y > 0 || y == -1} @-}
max2 :: List Int -> Int
max2 xs@(x :+: _) = foldr (\x y -> if x > y then x else y) x xs
max2 _ = -1

-- max3 :: List Int -> Maybe Int
-- max3 xs@(x :+: _) = Just $ foldr (\x y -> if x > y then x else y) x xs
-- max3 _ = Nothing