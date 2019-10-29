module GetNth where

import Prelude hiding (length)

data CList = Cons Int CList | Nil deriving Eq

getNth :: CList -> Int -> Int 
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = -1

length :: CList -> Int
length (Cons _ xs) = 1 + length xs
length Nil = 0

getNthContract :: CList -> Int -> Int -> Bool
getNthContract xs i _ = 0 <= i && i < length xs

-- Test 2: getNth assume getNthContract assert getNthAss -- works similarly for both
getNthInputA :: CList -> Int -> Int -> Bool
getNthInputA a b _ = (a == (Cons 6 (Cons 7 (Cons 9 (Cons 5 (Cons 3 (Cons 2 Nil))))))) && (b == 3)

getNthInputB :: CList -> Int -> Int -> Bool
getNthInputB a b _ = (a == (Cons 6 (Cons 7 (Cons 9 (Cons 5 Nil))))) && (b == 2)

getNthAssertA :: CList -> Int -> Int -> Bool
getNthAssertA _ _ res = res == 6
