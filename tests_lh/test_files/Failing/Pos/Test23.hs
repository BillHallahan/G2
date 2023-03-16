{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List ) where

import Prelude hiding (foldr, zipWith)

import qualified Data.Map as M

import Data.List (minimumBy)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | C a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
    size (C x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (C x xs) = x `op` b

a   :: List a -> List b -> List c
a Emp Emp               = Emp
a (C x xs) (C y ys) = Emp
a _          _          = die ""

d :: List Double -> List Double -> Double
d px py = foldr (+) 0 $ a px py

nearest   :: Int -> M.Map Int (List Double) -> List Double -> Int
nearest k centers p = fst $ minimumBy foldr (M.toList centers)
  where
    foldr x1 x2 = compare (d (snd x1) p) (d (snd x2) p)

test_nearest = nearest 3 (M.fromList [(0, C 0.0 Emp)]) (C 0.0 Emp)
