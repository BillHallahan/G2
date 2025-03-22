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
