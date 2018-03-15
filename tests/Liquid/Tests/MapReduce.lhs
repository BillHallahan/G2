Map-Reduce
==========

<div class="hidden">
\begin{code}
module MapReduce (mapReduce) where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1, length)
expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v
\end{code}
</div>

The following is a super simplified implementation of
[Map-Reduce](http://en.wikipedia.org/wiki/MapReduce)
using the [Lists](List.lhs) and `Data.Map`.

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)


{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ length :: xs:List a -> {v:Nat | v == size xs}  @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ map :: (a -> b) -> xs:List a -> ListX b xs @-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs


{-@ empty :: ListN a 0 @-}
empty = Emp

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs 


{-@ append :: xs:List a -> ys:List a ->
        {zs:List a | size zs == ((size xs) + (size ys)) } @-}
append Emp        ys = ys
append (x :+: xs) ys = x :+: (xs `append` ys)

{-@ measure sizeNest :: List (List a) -> Int
    sizeNest Emp = 0
    sizeNest ((:+:) x xs) = size x + sizeNest xs
  @-}

{-@ concat :: xs:List (List a) -> ListN a (sizeNest xs) @-}
--concat (x :+: xs) = x `append` concat xs
--concat Emp = Emp
concat = foldr (append) Emp

{-@ foldr1 :: (a -> a -> a) -> {xs:List a | size xs > 0 } -> a @-}
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"


{-@ foldr :: (a -> b -> b) -> b-> {xs:List a | size xs > 0 } -> b @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v

mapReduce fm fr xs = kvm
  where
    kvs      = expand      fm xs     -- step 1
    kvsm     = group       kvs       -- step 2
    kvm      = if length (M.elems kvsm) > 0
                 then collapse fr kvsm      -- step 3
                 else error "Must have a non empty list"
\end{code}

**The Problem** If you solved `foldr1` then you should
get a single type error below, in the call to `foldr1`
in `collapse`. Fix the error by **modifying the
refinement type specifications** only (do not modify any code).

**Note:** This problem requires you to have solved the
`foldr1` problem from [List.lhs](List.lhs); otherwise
no points.

Next, we briefly describe and show each step of the
`mapReduce` function.

Step 1: Map Elements into Key-Value Lists
-----------------------------------------

\begin{code}
{-@ expand  :: (a -> List (k, v)) -> List a -> List (k, v) @-}
expand f xs = concat (map f xs)
\end{code}

Step 2: Group By Key
--------------------

\begin{code}
{-@ group :: (Ord k) => List (k, v) -> M.Map k (List v) @-}
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = add v (M.findWithDefault empty k m)
\end{code}

Step 3: Reduce Each Key to Single Value
---------------------------------------

\begin{code}
{-@ collapse  :: (v -> v -> v) -> M.Map k {l:(List v) | size l > 0} -> M.Map k v @-}
collapse f = M.map (foldr1 f)

toList :: M.Map k v -> List (k, v)
toList = M.foldrWithKey (\k v acc -> add (k, v) acc) empty
\end{code}
