module MapReduce2 where

import Prelude hiding (concat, foldr, foldr1, map)

import qualified Data.Map as M

expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v

add       :: a -> List a -> List a
empty     :: List a

concat    :: List (List a) -> List a

map       :: (a -> b) -> List a -> List b


data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)


{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}


{-@ type ListN a N  = {v:List a | size v = N} @-}
{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v

mapReduce fm fr xs = kvm
  where
    kvs      = expand      fm xs     -- step 1
    kvsm     = group       kvs       -- step 2
    kvm      = if length M.empty > 0
               then collapse fr kvsm      -- step 3
               else error "Must have a non empty list"


{-@ expand  :: (a -> List (k, v)) -> List a -> List (k, v) @-}
expand f xs = concat (map f xs)


{-@ group :: (Ord k) => List (k, v) -> M.Map k (List v) @-}
group     = foldr addKV  M.empty

addKV :: Ord k => (k, v) -> M.Map k (List v) -> M.Map k (List v) 
addKV (k,v) m = M.insert k vs' m
  where
    vs'       = add v (M.findWithDefault empty k m)


collapse f = M.map (foldr1 f)


{-@ concat :: y:List (List a) -> List a @-}
concat Emp      = Emp
concat (x:+:xs) = cons_list x (concat xs)
  
cons_list (x:+:xs) ys = x :+: (cons_list xs ys)

{-@ empty :: ListN a 0 @-}
empty = Emp

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs

{-@ foldr1 :: (a -> a -> a) -> {x:List a | size x > 0} -> a @-}
foldr1 :: (a -> a -> a) -> List a -> a
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)


{-@ map :: (a -> b) -> x:List a -> ListX b x @-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs
