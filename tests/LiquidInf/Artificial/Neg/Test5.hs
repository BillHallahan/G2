{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where


import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

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

{-@ f :: Ord k => k -> b -> M.Map k (List b) -> M.Map k ({xs:List b | 0 < size xs}) @-}
f k v m = M.insert k (v :+: Emp) m
