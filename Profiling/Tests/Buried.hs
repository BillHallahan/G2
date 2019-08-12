module Buried where

data Buried a = Buried (Buried a) | Bottom a

dig :: Buried a -> a
dig (Bottom x) = x
dig (Buried x) = dig x

dig' :: Buried Int -> Int
dig' (Bottom x) = x
dig' (Buried x) = (dig' x) + 1

add :: Buried Int -> Buried Int -> Int
add x y = (dig x + dig y)

add' :: Buried Int -> Buried Int -> Int
add' x y = (dig' x + dig' y)

f :: (Int -> Int) -> Buried Int -> Buried Int -> Int
f g x y = g (add x y) 

add2 :: Buried Int -> Buried Int -> Int
add2 x y = (add x y) + 2
