module List4 where

import Prelude hiding (Num (..), drop, last, null, take, takeWhile, zip)

zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

p1 x xs ys = zip (x:xs) ys == zipConcat x xs ys

data Nat = S Nat | Z
  deriving (Show,Ord)

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

Z     + y = y
(S x) + y = S (x + y)

data AB = A | B

instance Eq AB where
    A == A = True
    B == B = True
    _ == _ = False

count :: AB -> [AB] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

p2 n xs = count n xs == count n (xs ++ [])

p3 n xs ys = count n xs + count n ys == count n (xs ++ ys)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

p4 xs = (takeWhile (\_ -> True) xs == xs)

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

notnull :: [a] -> Bool
notnull [] = False
notnull _  = True

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

p5 ys = given (notnull ys)
              (last ys == last ys)

drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

p6 n xs = take n xs ++ drop n xs == xs
