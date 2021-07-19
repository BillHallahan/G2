{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
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

foldl1 f (x :+: xs)    = foldl f x xs
foldl1 _ Emp        = die "foldl1"

foldl              :: (a -> b -> a) -> a -> List b -> a
foldl _ acc Emp     = acc
foldl f acc (x :+: xs) = foldl f (f acc x) xs

wtAverage :: List Int -> Int
wtAverage wxs = foldl1 (+) wxs

mWtAverage :: List Int -> Int
mWtAverage xs@(_ :+: _)  = wtAverage xs
mWtAverage Emp = 0