module ToList where

import qualified Data.Map as M

data List a = Emp
            | (:+:) a (List a)
            deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

toList :: M.Map k v -> List (k, v)
toList = M.foldrWithKey (\k v acc -> add (k, v) acc) empty

{-@ empty :: ListN a 0 @-}
empty = Emp


{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs

toList2 :: M.Map Int Int -> List Int
toList2 = M.foldr (\k acc -> acc) Emp