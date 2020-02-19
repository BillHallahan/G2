{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

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

{-@ type ListNE a = {v:List a | size v > 0} @-}

{-@ f :: (Ord k) => List (k, v) -> M.Map k (ListNE v) @-}
f :: (Ord k) => List (k,v) -> M.Map k (List v)
f xs = g xs

g :: (Ord k) => List (k, v) -> M.Map k (List v)
g (x :+: xs) = h x M.empty
g Emp = M.empty

h (k,v) m = M.insert k (v :+: Emp) m