module AddToEven where

import Prelude hiding (zipWith)

{-@ LIQUID "--no-termination" @-}

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g 5

-- Without the below refinement type for g, this file can not be verified
-- {-@ g :: Int -> Even @-}
-- {-@ g :: Int -> {v:Int | v /= -1} @-}
g :: Int -> Int
g x = x + x



data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ zipWith :: (a -> b -> c) -> v1:List a -> {v2:List b | size v1 > 0 => size v2 > 0} -> List c @-}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)


{-@ f2 :: {x:Int | x mod 2 = 0} @-}
f2 :: Int
f2 = g2

{-@ g2 :: Int @-}
g2 :: Int
g2 = 0

{-@ f3 :: Int -> Even @-}
f3 :: Int -> Int
f3 x = x + g3 x

-- Without the below refinement type for g, this file can not be verified
{-@ g3 :: Int -> Int @-}
g3 :: Int -> Int
g3 x = x

{-@ h :: {x:Int | x == 8} @-}
h :: Int
h = 6 + 2