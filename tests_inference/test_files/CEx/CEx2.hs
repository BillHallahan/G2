{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module CEx2 where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

infixr 9 :+:

map       :: (a -> b) -> List a -> List b
concat    :: List (List a) -> List a

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

map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys

expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v

mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v
mapReduce fm fr xs = kvm
  where
    kvs   = expand      fm xs     -- step 1
    kvsm  = group       kvs       -- step 2
    kvm   = collapse fr kvsm      -- step 3

expand f xs = concat (map f xs)

group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = v :+: (M.findWithDefault Emp k m)

{-@ collapse :: (v -> v -> v) -> m:(M.Map k {l : (List v) | false}) -> (M.Map k v) @-}
collapse f = M.map (foldr1 f)