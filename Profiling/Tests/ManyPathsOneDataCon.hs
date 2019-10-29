module StateMergingTests where

import qualified Data.List as L

data Tree a = Nil | Node (Tree a) a (Tree a) deriving Eq 

treeInsert :: (Ord a) => Tree a -> a -> Tree a
treeInsert Nil x = Node Nil x Nil
treeInsert (Node t1 y t2) x 
    | y == x = Node t1 y t2
    | y < x = Node t1 y (treeInsert t2 x)
    | otherwise = Node (treeInsert t1 x) y t2

treeSum :: Tree Int -> Int -> Int
treeSum t i = treeSum' (treeInsert t i)

treeSum' :: Tree Int -> Int
treeSum' t = case t of
    Nil -> 0
    Node t1 x t2 -> (treeSum' t1) + x + (treeSum' t2)

reverse' :: (Eq a) => [a] -> [a]
reverse' list = reverse'' list []
    where
        reverse'' [] reversed     = reversed
        reverse'' (x:xs) reversed = reverse'' xs (x:reversed)

compress :: (Eq a) => [a] -> [a]
compress (x:ys@(y:_))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

last' :: [a] -> a
last' [x] = x
last' (x:xs) = last' xs
last' [] = error "Empty list"

lastSums :: [Int] -> [Int] -> Int
lastSums a b = (last' a) + (last' b)

maybeLast :: [Int] -> Maybe Int
maybeLast [x] = case (x `mod` 2 == 0) of
    True -> Just x
    False -> Nothing
maybeLast (x:xs) = maybeLast xs
maybeLast [] = Nothing

maybeLastSnd :: [Int] -> [Int] -> Maybe Int
maybeLastSnd a b = case (maybeLast a) of 
    (Just _) -> (maybeLast b)
    Nothing -> (maybeLast b)

any' :: [Bool] -> Bool
any' [] = False
any' (x:xs) = case x of
    True -> True
    False -> any' xs
        
sumIfAny :: [Bool] -> [Int] -> Int
sumIfAny a b = case (any' a) of
    True -> sum b
    False -> product b

foldrSimple :: (a -> b -> b) -> b -> [a] -> b
foldrSimple f z [] = z
foldrSimple f z (x:xs) = f x (foldrSimple f z xs)

keepJust :: Int -> Maybe Int -> Maybe Int
keepJust a b = case b of
    Just x -> Just (x + a)
    Nothing -> Nothing

foldrTest :: Maybe Int -> [Int] -> Int
foldrTest z xs = case (foldrSimple keepJust z xs) of
    Just a -> a
    Nothing ->  0

isSubsequenceOf' :: (Eq a) => [a] -> [a] -> Bool
isSubsequenceOf' [] _ = True
isSubsequenceOf' _ [] = False
isSubsequenceOf' a@(x:a') (y:b) 
    | x == y    = isSubsequenceOf' a' b
    | otherwise = isSubsequenceOf' a b

subseqOfTest :: [Int] -> [Int] -> [Int] -> [Int]
subseqOfTest a b c = case (isSubsequenceOf' a b) of
    True -> compress c
    False -> c

intersectEq :: (Eq a) => [a] -> [a] -> [a]
intersectEq [] _ = []
intersectEq _  [] =  []
intersectEq xs ys =  [x | x <- xs, any (== x) ys]

retIfIntersect :: [Int] -> [Int] -> [Int]
retIfIntersect a b = case (intersectEq a b) of
    (x:xs) -> L.nub a
    [] -> L.nub b

filter' :: (a -> Bool) -> [a] -> [a]
filter' pred [] = []
filter' pred (x:xs)
    | pred x = x : filter' pred xs
    | otherwise = filter' pred xs

sumEvens :: [Int] -> Int
sumEvens = sum . filter' (\a -> a `mod` 2 == 0)

evens :: [Int] -> [Int]
evens = filter' (\a -> a `mod` 2 == 0)

lengthEvens :: [Int] -> Int
lengthEvens = sum . filter' (\a -> a `mod` 2 == 0)

lengthEvensAss :: [Int] -> Int -> Bool
lengthEvensAss _ b = b < 5


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

data B = B1 B | B2 B | Bot Int

dig2 :: B -> Int
dig2 (B1 b) = dig2 b
dig2 (B2 b) = dig2 b
dig2 (Bot a) = a

-- modest improvement in searchTest by merging all symb vars
search' :: (a -> Bool) -> [a] -> a
search' f (x:xs) = case f x of
    True -> x
    False -> search' f xs
search' _ [] = error "No element found"

searchTest :: [Int] -> [Int] -> [Int]
searchTest a b = take (search' (\x -> x `mod` 2 == 0) a) b

searchTest2 :: [Int] -> Int
searchTest2 a = (search' (\x -> x `mod` 2 == 0) a)

hofstadterM :: Int -> Int
hofstadterM n
    | n == 0 = 0
    | n > 0 = n - hofstadterF ( hofstadterM $ n - 1)
    | otherwise = 0

hofstadterF :: Int -> Int
hofstadterF n
    | n == 0 = 1
    | n > 0 = n - hofstadterM ( hofstadterF $ n - 1)
    | otherwise = 0
 
