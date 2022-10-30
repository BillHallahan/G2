module FoldrTests where

{-@ LIQUID "--no-termination" @-}

import Prelude hiding (foldr)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@  foldr :: (a -> b -> b) -> b -> List a -> b @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ max2 :: List { x:Int | x > 0} -> { y:Int | y > 0 || y == -1} @-}
max2 :: List Int -> Int
max2 xs@(x :+: _) = foldr (\x y -> if x > y then x else y) x xs
max2 _ = -1

{-@ max3 :: List { x:Int | x > 0} -> Maybe { y:Int | y > 0 } @-}
max3 :: List Int -> Maybe Int
max3 xs@(x :+: _) = Just (foldr (\x y -> if x > y then x else y) x xs)
max3 _ = Nothing


{-@ simpleFold :: List { x:Int | x > 0} -> { y:Int | y > 0} @-}
simpleFold :: List Int -> Int
simpleFold xs = foldr (\_ y -> y) 1 xs

data C a = C a

{-@ m :: {x:Int | x > 0} -> C { y:Int | y > 0 } @-}
m :: Int -> C Int
m x = C (f x)

{-@  f :: b -> b @-}
f :: b -> b
f b = b

{-@ m2 :: {x:Int | x > 0} -> C { y:Int | y > 0 } @-}
m2 :: Int -> C Int
m2 x = C (f2 x)

{-@  f2 :: Int -> Int @-}
f2 :: Int -> Int
f2 b = 256

{-@ m3 :: {x:Int | x > 0} -> C { y:Int | y > 0 } @-}
m3 :: Int -> C Int
m3 x = let f2x = f2 x in C f2x
