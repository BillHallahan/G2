{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}

module List where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

data List = Emp
          | C List
          deriving (Eq, Ord, Show)

length Emp = 0
length (C xs) = 1 + length xs

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length Emp == 0)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
