module Collapse where

import Prelude hiding (foldr, foldr1)
import qualified Data.Map as M

data List a = Emp
            | (:+:) a (List a)
            deriving (Eq, Ord, Show)


{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ collapse  :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v @-}
collapse f = M.map (foldr1 f)

{-@ foldr1 :: (a -> a -> a) -> {v:List a | size v > 0} -> a @-}
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ empty :: ListN a 0 @-}
empty = Emp

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

f :: Int -> Int -> Int
f x y = x + y