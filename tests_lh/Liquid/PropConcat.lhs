
<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
 
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

{-@ length :: xs:List a -> {len:Int | len = size xs} @-}
length            :: List a -> Int
length _        = 0

{-@ l1 :: List Int @-}
l1     = 1 :+: Emp

{-@ l0 :: List Int @-}
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
