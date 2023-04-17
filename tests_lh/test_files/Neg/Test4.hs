module Combined ( f) where

data C a = Emp | C a

{-@ measure size :: C a -> Int
        size (Emp) = 0
        size (C x) = 1 @-}

{-@ invariant {v:C a | 0 <= size v} @-}
{-@ invariant {v:C a | size v <= 1} @-}

f :: C Int -> Int
f = e

e (C x) = x
e Emp = die ""

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
