module WeightedAverage (mWtAverage, size) where
import Prelude hiding(foldl, foldl1, map, sum, head, tail, null, all)

data List a = a :+: List a | Emp

{-@ measure size @-}
size        :: List a -> Int
size Emp     =  0
size (_ :+: xs) =  1 + size xs

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ die :: {v:String | false} -> a @-}
die msg = error msg

divide     :: Int -> Int -> Int
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n


foldl1 f (x :+: xs)    = foldl f x xs
foldl1 _ Emp        = die "foldl1"

foldl              :: (a -> b -> a) -> a -> List b -> a
foldl _ acc Emp     = acc
foldl f acc (x :+: xs) = foldl f (f acc x) xs

sum :: List Int -> Int
sum xs  = foldl1 (+) xs

wtAverage :: List (Int, Int) -> Int
wtAverage wxs = divide totElems totWeight
  where
    elems     = map (\(w, x) -> w * x) wxs
    weights   = map (\(w, _) -> w    ) wxs
    totElems  = sum elems
    totWeight = sum weights

map           :: (a -> b) -> List a -> List b
map _ Emp      =  Emp
map f (x :+: xs)  =  f x :+: map f xs

{-@ mWtAverage :: List ({ x:Int | x > 0 }, { x:Int | x > 0 }) -> Maybe Int @-}
mWtAverage :: List (Int, Int) -> Maybe Int
mWtAverage xs@(_ :+: _)  = Just (wtAverage xs)
mWtAverage Emp = Nothing

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
