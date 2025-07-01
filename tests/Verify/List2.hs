module List2 where

data AB = A | B deriving Eq

initEq :: AB -> [AB] -> AB
initEq x [] = A
initEq x (y:ys) =
  case x == y of
    True -> initEq x ys
    _ -> B

p1 :: AB -> [AB]-> Bool
p1 n xs = initEq n xs == initEq n xs

p2 :: AB -> [AB] -> [AB] -> Bool
p2 n xs ys = initEq n (xs ++ ys) == initEq n (xs ++ ys)

p2False :: AB -> [AB] -> [AB] -> Bool
p2False n xs ys = initEq n (xs ++ ys) == initEq n (xs)