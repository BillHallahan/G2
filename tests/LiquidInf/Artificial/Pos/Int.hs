-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--maxparams=0"  @-}
{-@ LIQUID "--eliminate=all" @-}
module Int (usesF) where

import Prelude hiding (head)

{-@ usesF :: {x:Int | x > 0} -> { x:Int | x >= 0 } @-}
usesF = f

f :: Int -> Int
f 0 = die "bad Int"
f x = x

{-@ die :: {v:String | false} -> a @-}
die = error
