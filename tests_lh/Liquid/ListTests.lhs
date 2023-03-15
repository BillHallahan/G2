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
 

module Replicate where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

r :: L

data L = E
       | C L
       deriving (Eq, Ord, Show)

{-@ r :: L @-}
r = foldl (\_ _ -> E) E []

data ListI = EmpI
           | CI Int ListI
           deriving (Eq, Ord, Show)

{-@ measure sizeI      :: ListI -> Int
    sizeI (EmpI)        = 0
    sizeI (CI x xs) = 1 + sizeI xs
  @-}

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

{-@ lengthI :: {v:ListI | sizeI v >= 0} -> Int @-}
lengthI            :: ListI -> Int
lengthI EmpI      = 0
lengthI (CI x xs) = 1

{-@ map :: (Int -> Int) -> ListI -> ListI @-}
map       :: (Int -> Int) -> ListI -> ListI
map f EmpI       = EmpI
map f (CI x xs) = CI (f x) (map f xs)

{-@ prop_map :: (Int -> Int) -> ListI -> TRUE @-}
prop_map f xs = lAssert (0 <= lengthI (map f xs))

\end{code}

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ length :: xs:List a -> {v:Nat | v == size xs}  @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ append :: xs:List a -> ys:List a ->
        {zs:List a | size zs == ((size xs) + (size ys)) } @-}
append Emp        ys = ys
append (x :+: xs) ys = x :+: (xs `append` ys)

{-@ measure sizeNest :: List (List a) -> Int
    

  @-}

{-@ concat :: xs:List (List a) -> ListN a (sizeNest xs) @-}
concat    :: List (List a) -> List a
concat = foldr (append) Emp

\end{code}

\begin{code}
{-@ length_1 :: xs:List a -> Int  @-}
length_1            :: List a -> Int
length_1 Emp        = 0
length_1 (x :+: xs) = 1

prop_concat_1 :: Bool
prop_concat_1 = lAssert (length_1 xss == 0)
  where
    xss     = Emp
\end{code}
