-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--maxparams=0"  @-}
{-@ LIQUID "--eliminate=all" @-}
module Head (usesHead) where

import Prelude hiding (head)

{-@ die :: {v:String | false} -> a @-}
die = error

usesHead :: Int
usesHead = head [1, 2, 3]

head :: [a] -> a
head (x:_) = x
head _ = die "head: Bad call"

{-@ head2 :: xs:{ ys:[a] | 0 < len xs } -> a @-}
head2 :: [a] -> a
head2 (x:_) = x
head2 _ = die "head: Bad call"
