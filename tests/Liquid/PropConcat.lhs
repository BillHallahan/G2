
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
 

module PropConcat ( List
                  , foldr
                  , concat
                  ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

concat    :: List (List a) -> List a
\end{code}
</div>

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
\end{code}


\begin{code}
{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ length :: xs:List a -> {len:Int | len = size xs} @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: Emp

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ append :: x1: (List a) -> x2 : (List a) -> ListN a {1} @-}
append :: List a -> List a -> List a 
append Emp x2 = x2
append (x :+: xs) x2 = append xs (x :+: x2) 

{-@ concat :: List (List a) -> List a @-}
concat xs = foldr (\xs res -> append xs res) Emp xs

prop_concat = lAssert (length (concat xss) == 1)
  where
    xss     = l0 :+: l1 :+: Emp

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
\end{code}
