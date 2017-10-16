module GetNthPoly where

import Prelude hiding (length)

data CList a = Cons a (CList a) | Nil

getNthInt :: CList Int -> Int -> Int
getNthInt = getNth

getNth :: CList a -> Int -> a 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = error "Invalid index"

length :: CList a -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

getNthContract :: CList a -> Int -> Int -> Bool
getNthContract xs i _ = 0 <= i && i < length xs