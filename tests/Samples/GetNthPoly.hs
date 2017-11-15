module GetNthPoly where

import Prelude hiding (length)

data CList a = Cons !a (CList a) | Nil

data X = X

data Peano = Succ Peano | Zero

getNthX :: CList X -> Int -> X
getNthX x y = getNth x y

getNthPeano :: CList Peano -> Int -> Peano
getNthPeano x y = getNth x y

getNthInt :: CList Int -> Int -> Int
getNthInt x y = getNth x y

{-@ getNth :: xs:(CList  a) -> {n:Int | getNthContract xs n 0} -> Int @-}
getNth :: CList a -> Int -> a 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = error "Invalid index"

{-@ measure length @-}
length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

{-@ predicate getNthContract @-}
getNthContract :: CList a -> Int -> b -> Bool
getNthContract xs i _ = 0 <= i && i < length xs


{-@ project :: xs:(CList  Int) -> CList {i:Int | 0 <= i } -> Int @-}
-- project :: CList Int -> CList Int -> Int 
-- project xs is = sum (map (getNth xs) is)

-- CList {v:Int | p } -> Bool
-- clist_p_contract [] = True 
-- clist_p_contract (x:xs) = p x && clist_p_contract xs 

{-@ boject :: xs:(CList  Int) -> (Int -> {i:Int | 0 <= i }) -> Int @-}
{-@ boject :: xs:(CList  Int) -> (Int -> {i:Int | getNthContract xs i 0}) -> Int @-}

-- boject xs f = sum (map (getNth xs) is)
--   where 
--     is      = [f 0, f 1, f 2]

-- wrap f 