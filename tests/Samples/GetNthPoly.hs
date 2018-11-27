module GetNthPoly where

import Prelude hiding (length)

data CList a = Cons !a (CList a) | Nil deriving (Eq)

data IList = ICons Int IList

data X = X deriving (Eq)

data Peano = Succ Peano | Zero

-- data E a b = L a | B a

singleton :: a -> CList a
singleton x = Cons x Nil

getNthX :: CList X -> Int -> X
getNthX x y = getNth x y

getNthPeano :: CList Peano -> Int -> Peano
getNthPeano x y = getNth x y

-- getNthE :: CList (E Int Float) -> Int -> E Int Float
-- getNthE x y = getNth x y

getNthCListInt :: CList (CList Int) -> Int -> CList Int
getNthCListInt x y = getNth x y

getNthCListX :: CList (CList X) -> Int -> CList X
getNthCListX x y = getNth x y

getNthInt :: CList Int -> Int -> Int
getNthInt x y = getNth x y

{-@ getNth :: xs:(CList  a) -> {n:Int | getNthContract xs n 0} -> Int @-}
getNth :: CList a -> Int -> a 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = error "Invalid index"

getHead :: CList a -> a
getHead (Cons x _) = x
getHead _ = error "Empty CList passed to getHead."

getTail :: CList a -> CList a
getTail (Cons _ xs) = xs
getTail _ = error "Empty CList passed to getTail."

getHeadI :: IList -> Int
getHeadI (ICons x _) = x

{-@ measure length @-}
length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

{-@ predicate getNthContract @-}
getNthContract :: CList a -> Int -> b -> Bool
getNthContract xs i _ = 0 <= i && i < length xs


class CFunctor f where
    cfmap :: (a -> b) -> f a -> f b

    (<$!) :: a -> f b -> f a
    (<$!) x = cfmap (\_ -> x)

instance CFunctor CList where
    cfmap g (Cons x xs) = Cons (g x) (cfmap g xs)
    cfmap _ Nil = Nil

cfmapInt :: (Int -> Int) -> CList Int -> CList Int
cfmapInt f xs = cfmap f xs

double :: Int -> Int
double x = x * 2

add1 :: Int -> Int
add1 x = x + 1

intX :: Int -> X
intX _ = X

intCListInt :: Int -> CList Int
intCListInt x = Cons x Nil

cfmapIntX :: (Int -> X) -> CList Int -> CList X
cfmapIntX f xs = cfmap f xs

cfmapIntCListInt :: (Int -> CList Int) -> CList Int -> CList (CList Int)
cfmapIntCListInt f xs = cfmap f xs

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
