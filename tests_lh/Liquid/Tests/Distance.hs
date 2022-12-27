module Distance where

import qualified Data.Map as M

import Prelude hiding (zipWith, foldr)

data List a = Emp
            | (:+:) a (List a)
            deriving (Eq, Ord, Show)


{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ zipWith :: (a -> b -> c) -> xs:List a -> ListX b xs -> ListX c xs @-}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)


type Center  = Int
{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}

type Centering = M.Map Center Point
{-@ type CenteringKN K N = M.Map (CenterK K) (PointN N) @-}

type Point = List Double
{-@ type PointN N = ListN Double N @-}

{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> {x:CenterK k | x < k} @-}
nearest   :: Int -> Int -> Centering -> Point -> Center
nearest k n centers p = x
        where (x,y) = head $ M.toList t
              t = M.map (\a -> distance n a p) centers

{-@ distance :: n:Nat -> x:Point -> {y:Point | size x = size y} -> Double @-}
distance :: Int -> Point -> Point -> Double
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ distance2 :: x:Double -> Double @-}
distance2 :: Double -> Double
distance2 x = x^(3 :: Int)

{-@ distance3 :: x:Double -> {_:Double | false} @-}
distance3 :: Double -> Double
distance3 x = x^3

{-@ distance4 :: {_:Double | false} @-}
distance4 :: Double
distance4 = sqrt $ foldr2 (+) 0 Emp

foldr2 :: (a -> b -> b) -> b -> List a -> b
foldr2 _  b Emp        = b
foldr2 op b (x :+: xs) = b
