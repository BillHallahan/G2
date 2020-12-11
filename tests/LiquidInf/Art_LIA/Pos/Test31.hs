module Combined ( List, f) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List = Emp | C

{-@ measure size :: List -> Int
    size Emp = 0
    size C = 1
  @-}

{-@ invariant {v:List | 0 <= size v} @-}
{-@ invariant {v:List | size v <= 1} @-}

s :: List -> Int
s Emp  = 0
s C = 1

zipWith   :: List -> List -> List
zipWith Emp Emp = Emp
zipWith C C = C
zipWith _  _ = die  "Bad call to zipWith"

{-@ f :: List -> TRUE @-}
f xs = s xs == s (zipWith xs xs)