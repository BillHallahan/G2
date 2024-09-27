module PolyHigherOrder where

data List a = Cons a (List a) | EmptyList

f :: (List Bool -> List Bool) -> List Bool -> Bool
f g l = case g l of
    Cons True l -> True
    Cons False l -> False
    EmptyList -> True

h :: (Num a, Ord a) => (a -> a) -> Bool
h g = g 3 <= g 6

assoc :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
assoc op x y z = op (op x y) z == op x (op y z)

data Stream a = Stream a (Stream a)

streamTail :: Stream a -> Stream a
streamTail (Stream _ s) = s

sf :: (Stream a -> Int) -> Stream a -> Bool
sf f s = f s == f (streamTail s)

tupleTest :: (Num a, Ord a) => ((a, a) -> (a, a)) -> Bool
tupleTest f = let (a,b) = f (3,6) in not (a <= b)
