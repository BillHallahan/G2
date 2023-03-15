module Foldr1 where

import Prelude hiding (foldr1, foldr)
import qualified Data.Map as M

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ foldr1 :: (a -> a -> a) -> List a -> a @-}
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

h :: Int -> Int -> Int
h _ x = x
