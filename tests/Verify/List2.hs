module List2 where

import Prelude hiding (replicate)

data AB = A | B

instance Eq AB where
  A == A = True
  B == B = True
  _ == _ = False

initEq :: AB -> [AB] -> AB
initEq x [] = A
initEq x (y:ys) =
  case x == y of
    True -> initEq x ys
    _ -> B

data Nat = Succ Nat | Z

replicate :: Nat -> a -> [a]
replicate Z _ = []
replicate (Succ n) x = x:replicate n x

p1 :: AB -> [AB]-> Bool
p1 n xs = initEq n xs == initEq n xs

p2 :: AB -> [AB] -> [AB] -> Bool
p2 n xs ys = initEq n (xs ++ ys) == initEq n (xs ++ ys)

p3 :: Nat -> AB -> Bool
p3 n x = initEq x (replicate n x) == A

p2False :: AB -> [AB] -> [AB] -> Bool
p2False n xs ys = initEq n (xs ++ ys) == initEq n (xs)

p2False' :: AB -> [AB] -> [AB] -> Bool
p2False' n xs ys = initEq n (ys) == initEq n (xs ++ ys)

p3False :: Nat -> AB -> Bool
p3False n x = initEq x (replicate n x) == B

p3False' :: Nat -> AB -> Bool
p3False' Z _ = True
p3False' n x = initEq x (replicate n x) == B

p3False'' :: Nat -> AB -> AB -> Bool
p3False'' n x y = initEq x ((replicate n x) ++ [y]) == A
