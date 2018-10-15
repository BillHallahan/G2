
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

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ length :: xs:List a -> {len:Int | len = size xs} @-}
length            :: List a -> Int
length _        = 0

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: Emp

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ concat :: List (List a) -> List a @-}
concat xs = Emp

prop_concat = lAssert (length (concat xss) == 0)
  where
    xss     = l0 :+: l1 :+: Emp

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
\end{code}
