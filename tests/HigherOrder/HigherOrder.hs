{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# LANGUAGE BangPatterns #-}

module HigherOrder where

--import G2.Symbolic
--import ListTests

data List = Cons Bool List | EmptyList

getList :: List -> List
getList l = Cons True l

f :: (List -> List) -> List -> Bool
f g l = case g (getList l) of
    Cons False l -> True
    Cons True l -> False
    EmptyList -> True

myNot :: Bool -> Bool
myNot True = False
myNot False = True

h :: (Int -> Int) -> Bool
h g = myNot (g 3 <= g 6)

j :: (List -> Bool) -> Int
j f = case f EmptyList of
            True -> case f EmptyList of
                        True -> 1
                        _ -> 2
            _ -> 3

k :: (List -> Bool) -> List -> Int
k f l = case f l of
            True -> case f (Cons True l) of
                        False -> 0
                        _ -> 1
            _ -> 2

data AB = A AB | B deriving Eq

abc :: (AB -> AB) -> AB -> AB -> Int
abc f x y =
    case f x of
        A (A _) -> 1
        A _ -> 2
        _ -> case f y of
                B -> 3
                A (A (A (A _))) -> 4
                A (A _) -> 5
                _ -> 6

abc2 :: (Int -> AB) -> AB
abc2 f = case f 10 of
            A _ -> case f 20 of
                        B -> B
            _ -> A (A B)

{-# NOINLINE abInf #-}
abInf :: () -> AB
abInf = abInf

data XYZ = X | Y | Z

abc3 :: (Int -> AB -> XYZ) -> Int
abc3 f = case f 1 B of
                X -> case f 1 (A B) of
                            Y -> case f 2 (abInf ()) of
                                    Z -> 1
                                    _ -> 2
                            _ -> 3
                _ -> 4

{-# NOINLINE b #-}
b :: () -> AB
b () = A B

abc4 :: (Int -> AB -> XYZ) -> Int
abc4 f =
    case f 1 (A B) of
        X -> case f 1 (A (b ())) of
                Y -> 1
                _ -> 2
        _ -> 3

abc5 :: (Int -> AB -> AB -> XYZ) -> Int
abc5 f =
    case f 1 (A B) B of
        X -> case f 1 (A (b ())) (abInf ()) of
                Y -> 1
                _ -> 2
        _ -> 3

abc6 :: (Int -> AB) -> Int
abc6 f =
    case (f 1, f 1) of
        (A _, A _) -> 1
        _ -> 2

abc7 :: (Int -> AB) -> Int
abc7 f =
    case (f 1, f 1) of
        (A (A _), A (A _)) -> 1
        (A _, A _) -> 2
        _ -> 3

abc8 :: (Int -> AB) -> Int
abc8 f =
    case (f 1, f 1) of
        (A (A _), A (A _)) -> case f 2 of
                                    B -> 1
                                    _ -> 2
        (A _, A _) -> 3
        _ -> 4

abc9 :: (AB -> Int -> Maybe Int -> Bool) -> Int
abc9 f =
    case f (abInf ()) 1 (Just 1) of
        True -> case f (A B) 1 (Just 2) of
                    True -> case f B 1 (Just 2) of
                                False -> 1
                                _ -> 2
                    _ -> 3
        _ -> 4

assoc :: (Int -> Int -> Int) -> Int -> Int -> Int -> Bool
assoc op x y z = myNot (op (op x y) z == op x (op y z))

data Stream = Stream Bool Stream

streamTail :: Stream -> Stream
streamTail (Stream _ s) = s

sf :: (Stream -> Int) -> Stream -> Bool
sf f s = myNot (f s == f (streamTail s))

thirdOrder :: ((Bool -> Bool) -> Bool) -> Int
thirdOrder f =
    case not (f (\b -> case b of { True -> False; False -> True })) of
        True -> 1
        False -> 2

thirdOrder2 :: ((Bool -> Bool) -> Bool) -> Int
thirdOrder2 f =
    case f (\b -> case b of { True -> False; False -> True }) of
        True -> 1
        False -> if f (\b -> b) then 2 else 3

data IntPair = IntPair Int Int

tupleTestMono :: (IntPair -> IntPair) -> (Int, Bool)
tupleTestMono f = let (IntPair a b) = f (IntPair 3 6) in
                    case a <= b of
                        True -> (0, True)
                        False -> (1, False)

staggered :: (Int -> Int -> Int) -> Int
staggered f =
    let
        !g = f 1
    in
    g 2

multiPrim :: (Int -> Float -> Int) -> Int 
multiPrim f = case f 5 6.0 of 
                        5 -> 5
                        _ -> 8

{-callOtherMod :: Int -> Int
callOtherMod a = 
    let 
        x = minTest a
    in
        x + (assert (x /= 0) maxMap a)

testModAssert :: Int -> Int
testModAssert a = callOtherMod a

testRecursive :: (Int -> Float -> Int) -> Int
testRecursive f = testRecursive f -}

polyHigher :: ((a -> a) -> a) -> (a -> a) -> a
polyHigher g = g

inList :: [Int -> Int] -> Int -> [Int]
inList fs x = map (\f -> f x) fs 

retFunc :: [Int] -> [Int -> Int]
retFunc xs = map (\r x -> x + r) xs

data D = D Int | E Int

retFunc2 :: Int -> [Int] -> [Int -> Int]
retFunc2 n =
    let
        z = n + n
        y = if z > 10 then D z else E z
    in
    map (\r x -> case y of D z' -> x + r + z'; E _ -> x + r)

eqRetFunc :: [Int -> Int] -> [Int -> Int] -> Bool
eqRetFunc xs ys = map (\f -> f 0) xs == map (\f -> f 0) ys

funcGen :: ([Int] -> Int) -> [Int] -> Int
funcGen f xs =
    case f (g xs) of
        0 -> 0 -- line 1
        _ -> case f (g xs) of
                0 -> 1 -- Unreachable- requires that f (g xs) /= 0 (to not match on line 1)
                       -- and f (g xs) == 0 (to match on this line)
                _ -> 2
    where
        g [] = [f []]
        g (_:xs) = case f (g xs) of
                        1 -> [1]
                        _ -> g xs

repFix :: (Int -> Int) -> Int -> Int
repFix f x =
    case x == f x of
        True -> 1
        False -> repFix f (f x)

repF :: (Int -> Int -> Int) -> Int -> Int
repF f x =
    case f x (x * 2) of
        0 -> 1
        _ -> case f x (g (x + 1) (x * 2)) of
                0 -> 2
                _ -> 3
    where
        g a b = case f a (g a b) of
                    0 -> 1
                    _ -> 2

-- repCons is a tricky case where reducing an argument of f results in an additional call to f along all paths.
-- The way to get repCons to terminate is to not use the third argument of f.
repCons :: (Int -> Int -> Int) -> Int -> Int
repCons f x =
    case f (x * 2) inf of
        1 -> case f (x + 1) (g x) of
                2 -> 1
                _ -> 2
        _ -> 3
    where
        inf = inf

        g y = case f y inf of
                    1 -> g (y + 1)
                    _ -> g (y + 2)

repIte1 :: (Int -> Bool) -> (Int -> Int) -> Int
repIte1 f g =
    ite (\x -> f $ x + 1) (\x -> ite f g (g x)) 0
    where
        ite b a x | b x = a x
                  | otherwise = x

repIte2 :: (Int -> Bool) -> (Int -> Int) -> Int
repIte2 f g =
    ite (\x -> f $ x + 1) (\x -> ite f g (g x)) 0
    where
        ite b !a x | b x = a x
                   | otherwise = x