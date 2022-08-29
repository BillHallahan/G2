module HigherOrder where

data List = Cons Bool List | EmptyList

f :: (List -> List) -> List -> Bool
f g l = case g l of
    Cons True l -> True
    -- _ -> False
    Cons False l -> False
    EmptyList -> True

h :: (Int -> Int) -> Bool
h g = g 3 <= g 6

assoc :: (Int -> Int -> Int) -> Int -> Int -> Int -> Bool
assoc op x y z = op (op x y) z == op x (op y z)

data Stream = Stream Bool Stream

streamTail :: Stream -> Stream
streamTail (Stream _ s) = s

sf :: (Stream -> Int) -> Stream -> Bool
sf f s = f s == f (streamTail s)

thirdOrder :: ((Bool -> Bool) -> Bool) -> Bool
thirdOrder f = f (\b -> case b of { True -> False; False -> True })

data IntPair = IntPair Int Int

tupleTestMono :: (IntPair -> IntPair) -> Bool
tupleTestMono f = let (IntPair a b) = f (IntPair 3 6) in a <= b