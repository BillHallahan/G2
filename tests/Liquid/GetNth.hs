module GetNth where

import Prelude hiding (length)

data CList a = Cons !a (CList a) | Nil

data CList2 a = Cons2 a (CList2 a) | Nil2


getNthInt3 :: CList2 Int -> Int -> Int
getNthInt3 x y = getNth2 x y

{-@ getNth2 :: xs:CList2 a -> {n:Int | 0 < n } -> a @-}
getNth2 :: CList2 a -> Int -> a 
getNth2 (Cons2 _ xs) n = getNth2 xs n
getNth2 _      _ = die 0


data CList4 a = Cons4 a (CList4 a) | Nil4

getNth4 :: CList4 a -> Int -> a 
getNth4 (Cons4 _ xs) n = getNth4 xs n
getNth4 _      _ = die 0


{-@ getNth5 :: xs:CList a -> {n:Int | 0 < n} -> a @-}
getNth5 :: CList a -> Int -> a 
getNth5 (Cons x xs) n = getNth5 xs n
getNth5 _      _ = die 0

{-@ getNthInt :: xs:CList Int -> {n:Int | 0 <= n && n <= length xs} -> Int @-}
getNthInt :: CList Int -> Int -> Int
getNthInt x y = getNth x y

{-@ getNth :: xs:CList a -> {n:Int | 0 <= n && n <= length xs} -> a @-}
getNth :: CList a -> Int -> a 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = die 0

{-@ getNthInt2 :: xs:CList Int -> {n:Int | 0 <= n && n <= 1} -> Int @-}
getNthInt2 :: CList Int -> Int -> Int 
getNthInt2 (Cons x _)  0 = x 
getNthInt2 (Cons _ xs) n = getNthInt2 xs (n - 1)
getNthInt2 _      _ = die 0

{-@ measure length @-}
length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

{-@ die :: {x:Int | false} -> a @-}
die :: Int -> a
die x = error "die"

getHeadInt :: CList Int -> Int
getHeadInt xs = getHead xs

{-@ getHead :: xs:CList a -> a @-}
getHead :: CList a -> a
getHead (Cons x _) = x
getHead Nil = die 0

{-@ sumC :: CList {x:Int | x >= 0} -> {y:Int | y > 0} @-}
sumC :: CList Int -> Int
sumC (Cons x xs) = x + sumC' xs
sumC Nil = 0

sumC' :: CList Int -> Int
sumC' (Cons x xs) = x + sumC' xs
sumC' Nil = 0

{-@ sumCList :: Num a => CList {x:a | x >= 0} -> {y:a | y > 0} @-}
sumCList :: Num a => CList a -> a
sumCList (Cons x xs) = x + sumCList xs
sumCList Nil = 0

