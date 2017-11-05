-- Asserting sumAssert on sum will lead to a counterexample (with negative 
-- values in the list.)  If we use intPred to say that all the ints in the
-- CList are positive, alongside asserting sumAssert, the only counterexample
-- is sum Nil = 0.  If we run it alongside asserting sumAssert', there are no
-- counterexamples.
module PolyPred2 where

data CList a = Cons a (CList a) | Nil

intPred :: Int -> Bool
intPred x = 0 <= x

sumAssert :: CList Int -> Int -> Bool
sumAssert _ x = 0 < x

sumAssert' :: CList Int -> Int -> Bool
sumAssert' _ x = 0 < x

sum :: CList Int -> Int
sum x = sum' x 0

sum' :: CList Int -> Int -> Int
sum' (Cons x xs) y = sum' xs (x + y)
sum' Nil y = y