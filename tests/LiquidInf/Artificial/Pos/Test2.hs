{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type List0 a = {v:List a | size v = 0} @-}

{-@ empty :: List a @-}
empty     :: List a
empty = Emp

{-@ f :: M.Map Int (List0 Int) -> List0 Int -> Int @-}
f   :: M.Map Int (List Int) -> List Int -> Int
f _ _ = 1

g = f (M.fromList []) empty