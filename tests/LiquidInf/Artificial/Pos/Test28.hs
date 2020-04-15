{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List, mapReduce, f1, f2 ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import qualified Data.Map as M

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

data List a = Emp | (:+:) a (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))

foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss @-}

{-@ concat    :: xs:List (List a) -> { ys:List a | sizeXs xs == size ys } @-}
concat    :: List (List a) -> List a
concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

{-@ append :: xs:List a -> ys:List a -> { zs:List a | size xs + size ys == size zs } @-}
append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys

mapReduce :: (Ord k) => (a -> List (k, v)) -> (v -> v -> v) -> List a -> M.Map k v
mapReduce fm fr xs = kvm
  where
    kvs   = expand      fm xs
    kvsm  = group       kvs
    kvm   = collapse fr kvsm

expand   :: (a -> List (k, v)) -> List a -> List (k, v)
expand f xs = concat (map f xs)

f1 :: Int -> List (Int, Int)
f1 x = (x, x) :+: Emp

f2 :: Int -> List (Int, Int)
f2 x = (x, x) :+: (x, x) :+: Emp

f3 :: Int -> List (Int, Int)
f3 _ = Emp

group    :: (Ord k) => List (k, v) -> M.Map k (List v)
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = v :+: (M.findWithDefault Emp k m)

collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v
collapse f = M.map (foldr1 f)
