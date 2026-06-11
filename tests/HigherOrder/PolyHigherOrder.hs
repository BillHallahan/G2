module PolyHigherOrder where

data List a = Cons a (List a) | EmptyList

f :: (List Bool -> List Bool) -> List Bool -> Bool
f g l = case g l of
    Cons True l -> False
    Cons False l -> True
    EmptyList -> True

h :: (Num a, Ord a) => (a -> a) -> Bool
h g = not (g 3 <= g 6)

myNot :: Bool -> Bool
myNot True = False
myNot False = True

assoc :: Eq a => (a -> a -> a) -> a -> a -> a -> Bool
assoc op x y z = myNot (op (op x y) z == op x (op y z))

data Stream a = Stream a (Stream a)

streamTail :: Stream a -> Stream a
streamTail (Stream _ s) = s

sf :: (Stream a -> Int) -> Stream a -> Bool
sf f s = f s == f (streamTail s)

retStream :: (a -> a -> Stream a) -> a -> a -> [a]
retStream g x y =
    case g x y of
        Stream a (Stream b (Stream c (Stream d (Stream e _)))) -> [a, b, c, d, e]

retStream2 :: Eq a => (a -> a -> Stream a) -> a -> a -> [a]
retStream2 g x y =
    case (g x y, g y x) of
        (Stream a _, Stream b _)
            | a == b -> [a, a, a]
            | otherwise -> [b, b, b]


tupleTest :: (Num a, Ord a) => ((a, a) -> (a, a)) -> Bool
tupleTest f = let (a,b) = f (3,6) in not (a <= b)
