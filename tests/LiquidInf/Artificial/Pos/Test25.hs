{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
 

{-# LANGUAGE DeriveGeneric #-}

module ListQualif ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zip, repeat)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:


{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"


data List = Emp
          | (:+:) Int List
            deriving (Eq, Ord, Show)

{-@ measure size      :: List -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List | 0 <= size v} @-}

{-@ type ListN N  = {v:List | size v = N} @-}

length            :: List -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

zip :: List -> List -> List
zip Emp Emp               = Emp
zip (x :+: xs) (y :+: ys) = x :+: zip xs ys
zip _          _          = die  "Bad call to zipWith"

{-@ prop_zip :: List -> TRUE @-}
prop_zip :: List -> Bool
prop_zip xs = lAssert (length xs == length x2s)
  where
    x2s         = zip xs xs
