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

list1 :: (a -> Int) -> [a] -> Int
list1 f xs =
    case xs of
        [] -> 1
        x:xs' | f x > 10 -> 2
              | f x > 0 -> 3
              | f x + 100 > 20 -> 4
              | otherwise -> case xs' of
                                [] -> 5
                                y:_ | f x > f y -> 6
                                    | f y > f x -> 7
                                    | otherwise -> 8

list2 :: ([Int] -> [Int]) -> [Int] -> Int
list2 f xs =
    case f xs of
        [] -> 1
        [1, 2, 3] -> 2
        [1, 2, _] -> 3
        [1, _, _] -> 4
        _:_:_:_ -> 5
        _:_:_ -> 6
        (x:xs) -> case f (x:xs) of
                        [] -> 7
                        [1, 2, 3] -> 8
                        [1, 2, _] -> 9
                        [1, _, _] -> 10
                        (7:_:_:_) -> 11
                        (_:_:_:_) -> 12
                        (_:_:_) -> 13
                        (_:_) -> 14

list3 :: (a -> a -> Bool) -> (a -> a) -> ([a] -> [a]) -> (Maybe a -> a) -> a -> a -> Int
list3 c fi fl fm x y =
    case fl [x, fm (Just y), x] of
        [] -> 1
        (z:_) -> case fi z `c` fi y of
                    True -> let
                                a = fm (Just z)
                                z = fm Nothing
                            in
                            case a `c` a == z `c` z of
                                True -> 2
                                False -> 3
                    False -> case fi y `c` fi z of
                                    True -> 4
                                    False -> 5