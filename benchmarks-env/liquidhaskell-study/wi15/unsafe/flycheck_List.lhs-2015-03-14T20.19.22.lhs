Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

-- CHECKBINDER prop_size
-- CHECKBINDER empty
-- CHECKBINDER add
-- CHECKBINDER singleton
-- CHECKBINDER prop_replicate
-- CHECKBINDER prop_map
-- CHECKBINDER foldr1
-- CHECKBINDER prop_zipWith
-- CHECKBINDER prop_concat
 

module List ( List
, snd1
            , empty
            , add
            , singleton
            , map
            , replicate
            , foldr
            , foldr1
            , zipWith
            , concat
            ) where

import Assert
import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

empty     :: List a
add       :: a -> List a -> List a
singleton :: a -> List a
replicate :: Int -> a -> List a
map       :: (a -> b) -> List a -> List b
zipWith   :: (a -> b -> c) -> List a -> List b -> List c
concat    :: List (List a) -> List a
\end{code}
</div>

A Sized List Datatype
---------------------

Lets cook up our own `List` data type from scratch:

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
\end{code}

We can write a **measure** that logically represents
the *size*, i.e. number of elements of a `List`:

\begin{code}
{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}
\end{code}

It will be helpful to have a few abbreviations. First,
lists whose size is equal to `N`

\begin{code}
{-@ type ListN a N  = {v:List a | size v = N} @-}
\end{code}
and then, lists whose size equals that of *another* list `Xs`:

\begin{code}
{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}
\end{code}

(a) Computing the Length of a List
----------------------------------

Write down a *refined* type for `length`:

\begin{code}
{-@ length :: xs:List a -> {len:Int | len = size xs} @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs
\end{code}

such that the following type checks:

\begin{code}

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length l3 == 3)

{-@ l3 :: ListN Int 3 @-}
l3     = 3 :+: l2

{-@ l2 :: ListN Int 2 @-}
l2     = 2 :+: l1

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: l0

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int
\end{code}


(b) Constructing Lists
----------------------

Fill in the implementations of the following functions so that
LiquidHaskell verifies respect the given type signatures:

\begin{code}
{-@ empty :: ListN a 0 @-}
empty = Emp

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs

{-@ singleton :: a -> ListN a 1 @-}
singleton x = x :+: Emp  
\end{code}

(c) Replicating Values
----------------------

Fill in the code, and update the refinement type specification
for `replicate n x` which should return a `List` `n` copies of
the value `x`:

\begin{code}
{-@ replicate :: n:Int -> a -> ListN a {n} @-}
replicate 0 x = Emp
replicate n x = x :+: (replicate (n-1) x)
\end{code}

When you are done, the following assertion should be verified by LH.

\begin{code}
{-@ prop_replicate :: Nat -> a -> TRUE @-}
prop_replicate n x = lAssert (n == length (replicate n x))
\end{code}

(d) Map
-------

Fix the specification for `map` such that the assertion in `prop_map`
is verified by LH. (This will require you to first complete part (a) above.)

\begin{code}
{-@ map :: (a -> b) -> xs:(List a) ->{ ys:List b | size ys = size xs}@-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))
\end{code}

(e) Fold
--------

Fix the specification for `foldr1` so that the call to `die` is
verified by LH:

\begin{code}
{-@ foldr1 :: (a -> a -> a) -> {xs:List a| size xs > 0} -> a @-}
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)
\end{code}

(f) ZipWith
-----------

Fix the specification of `zipWith` so that LH verifies:

+ The call to `die` inside `zipWith` and
+ The assert inside `prop_zipwith`.

\begin{code}
{-@ zipWith :: (a -> b -> c) -> x1:(List a) -> {x2:List b | size x1 = size x2} -> {x3: List c | size x3 = size x1 } @-}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ prop_zipWith :: Num a => List a -> TRUE @-}
prop_zipWith xs = lAssert (length xs == length x2s)
  where
    x2s         = zipWith (+) xs xs
\end{code}

(g) List Concatenation *(Hard?)*
--------------------------------

Fill in the (refinement type) specification and
implementation for the function `concat` such that
when you are done, the assert inside `prop_concat`
is verified by LH. Feel free to write any other code
or specification (types, measures) that you need.



{-@ measure concatHelperMeasure @-}
{-@ concatHelperMeasure                        :: List a (List a)  -> Int @-}
concatHelperMeasure Emp =  0
concatHelperMeasure (Emp :+: xs2) = concatHelperMeasure xs2
concatHelperMeasure ((x1 :+: xs1) :+: xs2) = 1 + concatHelperMeasure (xs2)


{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}
\begin{code}


{-@ measure sample       :: (a -> Int) -> List a -> Int @-}
sample f (Emp)        = 0
sample f (x :+: xs) = f x + sample f xs



{-@ measure sample2       ::   List (List a) -> Int @-}
sample2  Emp = 0
sample2 (x1 :+: Emp) = length x1
sample2  (x1 :+: (x2 :+: xs )) = sample2 ((append x1 x2) :+: xs)



{-@ append :: x1: (List a) -> x2 : (List a) -> ListN a {size x1 + size x2} @-}
append :: List a -> List a -> List a 
append Emp x2 = x2
append (x :+: xs) x2 = append xs (add x x2)

{-@ partition :: _ -> xs:_ -> {v:_ | Sum3 v (size xs)} @-}
partition          :: (a -> Bool) -> List a -> (List a, List a)
partition _ Emp     = (Emp, Emp)
partition f (x:+:xs)
  | f x            = (x :+: ys, zs)
  | otherwise      = (ys, x :+: zs)
  where
    (ys, zs)       = partition f xs


{-@ measure fst1 @-}
fst1  (x, _) = x

{-@ measure snd1 @-}
snd1 (_, y) = y



{-@ predicate Sum3 X N = size (fst1 X) + size (snd1 X) = N @-}

{-@ predicate Sum4 X R = sample4 X = R @-}


{-@ sample3  ::  xs: List (List a) -> {v:Int | v= sample2 xs} @-}
sample3  Emp = 0
sample3 (x1 :+: Emp) = length x1
sample3  (x1 :+: (x2 :+: xs )) = sample3 ((append x1 x2) :+: xs)


{-@ measure sample4      :: List (List a) -> Int
    sample4 (Emp)        = 0
    sample4 ((:+:) x xs) = 1 + sample4 xs
  @-}



{-@ concatHelper :: x1: List a -> xs: List (List a) -> {res:List a | sample4 xs = size res} @-} 
concatHelper :: List a -> List (List a) -> List a
concatHelper x1 Emp = Emp
concatHelper x1 (x2 :+: xs) = append x2 x1

{-@ concat :: xs:List (List a) -> {res:List a | Sum2 xs res} @-}
concat Emp = Emp
concat (x1 :+: Emp) =  x1
concat (x1 :+: (x2 :+: xs )) =  concat  ((append x1 x2) :+: xs)

{-@ predicate Sum2 X N  =  (sample2 X) = size N @-}
{-@ predicate Sum X N  =  sample size X = size N @-}




prop_concat = lAssert (length (concat xss) == 6)
  where
    xss     = l0 :+: l1 :+: l2 :+: l3 :+: Emp
\end{code}
