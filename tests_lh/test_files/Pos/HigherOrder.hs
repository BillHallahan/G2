module Test ( List, f) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

foldr1 :: (a -> a -> a) -> List a -> a
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

{-@ type PointN N = {x:Int | x == n} @-}

{-@ call :: n:Int -> (Int, Int) -> (Int, Int) -> (Int, Int) @-}
call :: Int -> (Int, Int) -> (Int, Int) -> (Int, Int)
call n (n1, p1) (n2, p2) =
    case p1 == n && p2 == n of
        True -> (n1, p1)
        False -> die "call"

{-@ f :: n:Nat -> { xs:List (Int, {x:Int | x == n}) | size xs > 0 } -> (Int, {x:Int | x == n}) @-}
f :: Int -> (List (Int, Int)) -> (Int, Int)
f n ps = foldr1 (call n) ps