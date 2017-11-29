module GetNth where

import Prelude hiding (length)

data CList a = Cons !a (CList a) | Nil

getNthInt :: CList Int -> Int -> Int
getNthInt x y = getNth x y

{-@ getNth :: xs:CList a -> {n:Int | 0 <= n && n <= length xs} -> a @-}
getNth :: CList a -> Int -> a 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = die 0

{-@ measure length @-}
length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

{-@ die :: {x:Int | false} -> a @-}
die :: Int -> a
die x = error "die"