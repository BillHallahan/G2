-- Property from "Productive Use of Failure in Inductive Proof",
-- Andrew Ireland and Alan Bundy, JAR 1996
{-# LANGUAGE TypeOperators #-}
module Prod where

import Prelude(Bool(..), Int, (+), (*), (-), (>), (/=), (==), (<=), even, div, Eq, id, error)

import Prelude ((>=), mod)
import G2.Plugin hiding ((==>))
import G2.Plugin.Unsafe

{-# ANN module ("--smt-tuples --higher-order uninterpreted --smt cvc5,z3 --time 90")
    #-}

-- code here adapted from HipSpec.hs

infix 1 =:=

infixr 0 ==>

-- simplification to remove Equality / Prop type

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

givenBool :: Bool -> Bool -> Bool
givenBool = given

(==>) :: Bool -> Bool -> Bool
(==>) = given

proveBool :: Bool -> Bool
proveBool lhs = lhs =:= True

(=:=) :: Eq a => a -> a -> Bool
(=:=) = (==)

-- end of code from Tip module

-- Definitions

-- Booleans

otherwise = True

True && x = x
_    && _ = False

False || x = x
_     || _ = True

not True = False
not False = True

infix 4 ===
x === y = x == y

bool :: Bool -> Bool
bool = id

-- Nats

type Nat = Int

-- instance Arbitrary Nat where
--     arbitrary =
--         let nats = iterate S Z
--         in  (nats !!) `fmap` choose (0,5)

{-
instance Partial Nat where
    unlifted Z     = return Z
    unlifted (S x) = fmap S (lifted x)
-}

-- (+) :: Nat -> Nat -> Nat
-- Z + y = y
-- (S x) + y = S (x + y)

-- (*) :: Nat -> Nat -> Nat
-- Z * _ = Z
-- (S x) * y = y + (x * y)

-- (==),(/=) :: Nat -> Nat -> Bool
-- Z   == Z   = True
-- Z   == _   = False
-- S _ == Z   = False
-- S x == S y = x == y

-- x /= y = not (x == y)

-- (<=) :: Nat -> Nat -> Bool
-- Z   <= _   = True
-- _   <= Z   = False
-- S x <= S y = x <= y

one, zero :: Nat
zero = 0
one  = 1

double :: Nat -> Nat
double x = x + x

-- even :: Nat -> Bool
-- even Z         = True
-- even (S Z)     = False
-- even (S (S x)) = even x

half :: Nat -> Nat
half x = x `div` 2

mult :: Nat -> Nat -> Nat -> Nat
mult x y _ = x * y

fac :: Nat -> Nat
fac 0 = 1
fac x = x * fac (x - 1)

qfac :: Nat -> Nat -> Nat
qfac 0 acc = acc
qfac x acc = qfac (x - 1) (x * acc)

exp :: Nat -> Nat -> Nat
exp _ 0 = 1
exp x n = x * exp x (n - 1)

qexp :: Nat -> Nat -> Nat -> Nat
qexp x 0 acc = acc
qexp x n acc = qexp x (n - 1) (x * acc)

-- Lists

{-# ANN length (SMTEquivIs "lengthSMT") #-}
length :: [a] -> Nat
length []     = 0
length (_:xs) = 1 + (length xs)

lengthSMT :: [a] -> Nat
lengthSMT = smtLen

{-# ANN (++) (SMTEquivIs "appendSMT") #-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

appendSMT :: [a] -> [a] -> [a]
appendSMT = ($++)

{-# ANN drop (SMTEquivIs "dropSMT") #-}
drop :: Nat -> [a] -> [a]
drop x xs | x <= 0 = xs
drop _ [] = []
drop x (_:xs) = drop (x - 1) xs

dropSMT :: Nat -> [a] -> [a]
dropSMT n xs = 
  if n >= 0
    then smtExtract xs n ((smtLen xs) - n)
    else xs

{-# ANN rev (SMTEquivIs "revSMT") #-}
rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

revSMT :: [a] -> [a]
revSMT = smtReverse

{-# ANN qrev (SMTEquivIs "qrevSMT") #-}
qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

qrevSMT :: [a] -> [a] -> [a]
qrevSMT xs ys = smtReverse xs $++ ys


{-# ANN revflat (SMTEquivIs "revflatSMT") #-}
revflat :: [[a]] -> [a]
revflat []           = []
revflat (xs:xss)     = revflat xss ++ rev xs

revflatSMT :: [[a]] -> [a]
revflatSMT = smtFoldLeft (\acc xs -> smtReverse xs $++ acc) []

{-# ANN qrevflat (SMTEquivIs "qrevflatSMT") #-}
qrevflat :: [[a]] -> [a] -> [a]
qrevflat []           acc = acc
qrevflat (xs:xss)     acc = qrevflat xss (rev xs ++ acc)

qrevflatSMT :: [[a]] -> [a] -> [a]
qrevflatSMT xs ac = smtFoldLeft (\acc xs -> smtReverse xs $++ acc) [] xs ++ ac

{-# ANN rotate (SMTEquivIs "rotateSMT") #-}
rotate :: Nat -> [a] -> [a]
rotate 0     xs     = xs
rotate _     []     = []
rotate n     (x:xs) = rotate (n - 1) (xs ++ [x])

rotateSMT :: Nat -> [a] -> [a]
rotateSMT n xs = let k = n `mod` smtLen xs in smtExtract xs n (smtLen xs - n) $++ smtExtract xs 0 n

{-# ANN elem (SMTEquivIs "elemSMT") #-}
elem :: Nat -> [Nat] -> Bool
elem _ []     = False
elem n (x:xs) = (n == x) || elem n xs

elemSMT :: Nat -> [Nat] -> Bool
elemSMT n xs = smtContains xs [n]

subset :: [Nat] -> [Nat] -> Bool
subset []     ys = True
subset (x:xs) ys = x `elem` ys && subset xs ys

{-# ANN intersect (SMTEquivIs "intersectSMT") #-}
intersect :: [Nat] -> [Nat] -> [Nat]
(x:xs) `intersect` ys | x `elem` ys = x:(xs `intersect` ys)
                      | otherwise = xs `intersect` ys
[] `intersect` ys = []

intersectSMT :: [Nat] -> [Nat] -> [Nat]
intersectSMT xs ys = smtFoldLeft (\acc x -> if smtContains ys [x] then acc $++ [x] else acc) [] xs

{-# ANN union (SMTEquivIs "unionSMT") #-}
union :: [Nat] -> [Nat] -> [Nat]
union (x:xs) ys | x `elem` ys = union xs ys
                | otherwise = x:(union xs ys)
union [] ys = ys

unionSMT :: [Nat] -> [Nat] -> [Nat]
unionSMT xs ys = smtFoldLeft (\acc x -> if smtContains ys [x] then acc else acc $++ [x]) [] xs $++ ys

isort :: [Nat] -> [Nat]
isort [] = []
isort (x:xs) = insert x (isort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

{-# ANN count (SMTEquivIs "countSMT") #-}
count :: Nat -> [Nat] -> Nat
count n (x:xs) | n == x = 1 + (count n xs)
               | otherwise = count n xs
count n [] = 0

countSMT :: Nat -> [Nat] -> Nat
countSMT e xs = (smtLen xs) - (smtLen (smtReplaceAll xs [e] []))

sorted :: [Nat] -> Bool
sorted (x:y:xs) = (x <= y) && sorted (y:xs)
sorted _        = True

-- end Definitions

-- Lemmas

-- prop_L01 :: Nat -> Nat -> Bool
-- prop_L01 x y =
--   x + (S y) === S (x + y)

{-# ANN prop_L02 Prop #-}
prop_L02 :: Eq a => [a] -> a -> [a] -> Bool
prop_L02 xs y ys =
  length (xs ++ (y:ys)) === (1 + (length (xs ++ ys)))

{-# ANN prop_L03 Prop #-}
prop_L03 :: Eq a => [a] -> a -> Bool
prop_L03 xs y =
  length (xs ++ (y : [])) === (1 + (length xs))

{-# ANN prop_L04 Prop #-}
prop_L04 :: Eq a => Nat -> Nat -> a -> [a] -> Bool
prop_L04 w x y zs
  | w >= 0, x >= 0 = drop (w + 1) (drop x (y:zs)) === drop w (drop x zs)
  | otherwise = True

{-# ANN prop_L04_bad Prop #-}
prop_L04_bad :: Eq a => Nat -> Nat -> a -> [a] -> Bool
prop_L04_bad w x y zs =
  drop (w + 1) (drop x (y:zs)) === drop w (drop x zs)

-- prop_L05 :: Nat -> Nat -> a -> a -> [a] -> Bool
-- prop_L05 v w x y zs =
--   drop (S v) (drop (S w) (x : (y : zs))) === drop (S v) (drop w (x : zs))

-- prop_L06 :: Nat -> Nat -> Nat -> a -> [a] -> Bool
-- prop_L06 v w x y z =
--   drop (S v) (drop w (drop x (y:z))) === drop v (drop w (drop x z))

-- prop_L07 :: Nat -> Nat -> Nat -> a -> a -> [a] -> Bool
-- prop_L07 u v w x y z =
--   drop (S u) (drop v (drop (S w) (x : (y : z)))) ===
--   drop (S u) (drop v (drop w (x:z)))

{-# ANN prop_L08 Prop #-}
prop_L08 :: Eq a => [a] -> a -> Bool
prop_L08 x y =
  rev (x ++ (y : [])) === y : (rev x)

{-# ANN prop_L09 Prop #-}
prop_L09 :: Eq a => [a] -> [a] -> a -> Bool
prop_L09 x y z =
  rev (x ++ (y ++ (z : []))) === z : (rev (x ++ y))

{-# ANN prop_L10 Prop #-}
prop_L10 :: Eq a => [a] -> a -> Bool
prop_L10 x y =
  rev ((x ++ (y : [])) ++ []) === y : (rev (x ++ []))

{-# ANN prop_L11 Prop #-}
prop_L11 :: Eq a => [a] -> a -> [a] -> Bool
prop_L11 x y z =
  (x ++ (y : [])) ++ z === x ++ (y : z)

{-# ANN prop_L12 Prop #-}
prop_L12 :: Nat -> [Nat] -> Bool
prop_L12 x y =
  sorted y ==> sorted (insert x y)

{-# ANN prop_L13 Prop #-}
prop_L13 :: Eq a => [a] -> [a] -> a -> Bool
prop_L13 x y z =
  (x ++ y) ++ (z : []) === x ++ (y ++ (z : []))

{-# ANN prop_L14 Prop #-}
prop_L14 :: Eq a => [a] -> a -> a -> [a] -> Bool
prop_L14 w x y z =
  even (length (w ++ z)) === even (length (w ++ (x : (y : z))))

{-# ANN prop_L15 Prop #-}
prop_L15 :: Eq a => [a] -> a -> a -> [a] -> Bool
prop_L15 w x y z =
  length (w ++ (x : (y : z))) === (2 + (length (w ++ z)))

-- prop_L16 :: Nat -> Nat -> Bool
-- prop_L16 x y =
--   even (x + y) === even (x + S (S y))

-- prop_L17 :: Nat -> Nat -> Bool
-- prop_L17 x y =
--   x + S (S y) === S (S (x + y))

{-# ANN prop_L18 Prop #-}
prop_L18 :: Nat -> [Nat] -> Bool
prop_L18 x y =
  length (insert x y) === (1 + (length y))

{-# ANN prop_L19 Prop #-}
prop_L19 :: Nat -> Nat -> [Nat] -> Bool
prop_L19 x y z =
  x /= y ==> (x `elem` insert y z ==> x `elem` z)

{-# ANN prop_L20 Prop #-}
prop_L20 :: Nat -> [Nat] -> Bool
prop_L20 x y =
  count x (insert x y) === (1 + (count x y))

{-# ANN prop_L21 Prop #-}
prop_L21 :: Nat -> Nat -> [Nat] -> Bool
prop_L21 x y z =
  x /= y ==> count x (insert y z) === count x z

{-# ANN prop_L22 Prop #-}
prop_L22 :: Eq a => [a] -> [a] -> [a] -> Bool
prop_L22 xs ys zs =
  (xs ++ ys) ++ zs === xs ++ (ys ++ zs)

-- prop_L23 :: Nat -> Nat -> Nat -> Bool
-- prop_L23 x y z =
--   (x * y) * z === x * (y * z)

-- prop_L24 :: Nat -> Nat -> Nat -> Bool
-- prop_L24 x y z =
--   (x + y) + z === x + (y + z)


-- Theorems

-- prop_T01 :: Nat -> Bool
-- prop_T01 x = double x === x + x

{-# ANN prop_T02 Prop #-}
prop_T02 :: Eq a => [a] -> [a] -> Bool
prop_T02 x y = length (x ++ y ) === length (y ++ x)

{-# ANN prop_T03 Prop #-}
prop_T03 :: Eq a => [a] -> [a] -> Bool
prop_T03 x y = length (x ++ y ) === length (y ) + length x

{-# ANN prop_T04 Prop #-}
prop_T04 :: Eq a => [a] -> Bool
prop_T04 x = length (x ++ x) === double (length x)

{-# ANN prop_T05 Prop #-}
prop_T05 :: Eq a => [a] -> Bool
prop_T05 x = length (rev x) === length x

{-# ANN prop_T06 Prop #-}
prop_T06 :: Eq a => [a] -> [a] -> Bool
prop_T06 x y = length (rev (x ++ y )) === length x + length y

{-# ANN prop_T07 Prop #-}
prop_T07 :: Eq a => [a] -> [a] -> Bool
prop_T07 x y = length (qrev x y) === length x + length y

{-# ANN prop_T08 Prop #-}
prop_T08 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_T08 x y z = drop x (drop y z) === drop y (drop x z)

{-# ANN prop_T09 Prop #-}
prop_T09 :: Eq a => Nat -> Nat -> [a] -> Nat -> Bool
prop_T09 x y z w = drop w (drop x (drop y z)) === drop y (drop x (drop w z))

{-# ANN prop_T10 Prop #-}
prop_T10 :: Eq a => [a] -> Bool
prop_T10 x = rev (rev x) === x

{-# ANN prop_T11 Prop #-}
prop_T11 :: Eq a => [a] -> [a] -> Bool
prop_T11 x y = rev (rev x ++ rev y) === y ++ x

{-# ANN prop_T12 Prop #-}
prop_T12 :: Eq a => [a] -> [a] -> Bool
prop_T12 x y = qrev x y === rev x ++ y

{-# ANN prop_T13 Prop #-}
prop_T13 :: Nat -> Bool
prop_T13 x = half (x + x) === x

-- This property is the same as isaplanner #78
prop_T14 :: [Nat] -> Bool
prop_T14 x = bool (sorted (isort x))

-- prop_T15 :: Nat -> Bool
-- prop_T15 x = x + S x === S (x + x)

-- prop_T16 :: Nat -> Bool
-- prop_T16 x = bool (even (x + x))

{-# ANN prop_T17 Prop #-}
prop_T17 :: Eq a => [a] -> [a] -> Bool
prop_T17 x y = rev (rev (x ++ y)) === rev (rev x) ++ rev (rev y)

{-# ANN prop_T18 Prop #-}
prop_T18 :: Eq a => [a] -> [a] -> Bool
prop_T18 x y = rev (rev x ++ y) === rev y ++ x

{-# ANN prop_T19 Prop #-}
prop_T19 :: Eq a => [a] -> [a] -> Bool
prop_T19 x y = rev (rev x) ++ y === rev (rev (x ++ y))

{-# ANN prop_T20 Prop #-}
prop_T20 :: Eq a => [a] -> Bool
prop_T20 x = bool (even (length (x ++ x)))

{-# ANN prop_T21 Prop #-}
prop_T21 :: Eq a => [a] -> [a] -> Bool
prop_T21 x y = rotate (length x) (x ++ y) === y ++ x

{-# ANN prop_T22 Prop #-}
prop_T22 :: Eq a => [a] -> [a] -> Bool
prop_T22 x y = even (length (x ++ y)) === even (length (y ++ x))

{-# ANN prop_T23 Prop #-}
prop_T23 :: Eq a => [a] -> [a] -> Bool
prop_T23 x y = half (length (x ++ y)) === half (length (y ++ x))

-- prop_T24 :: Nat -> Nat -> Bool
-- prop_T24 x y = even (x + y) === even (y + x)

{-# ANN prop_T25 Prop #-}
prop_T25 :: Eq a => [a] -> [a] -> Bool
prop_T25 x y = even (length (x ++ y)) === even (length y + length x)

-- prop_T26 :: Nat -> Nat -> Bool
-- prop_T26 x y = half (x + y) === half (y + x)

{-# ANN prop_T27 Prop #-}
prop_T27 :: Eq a => [a] -> Bool
prop_T27 x = rev x === qrev x []

{-# ANN prop_T28 Prop #-}
prop_T28 :: Eq a => [[a]] -> Bool
prop_T28 x = revflat x === qrevflat x []

{-# ANN prop_T29 Prop #-}
prop_T29 :: Eq a => [a] -> Bool
prop_T29 x = rev (qrev x []) === x

{-# ANN prop_T30 Prop #-}
prop_T30 :: Eq a => [a] -> Bool
prop_T30 x = rev (rev x ++ []) === x

{-# ANN prop_T31 Prop #-}
prop_T31 :: Eq a => [a] -> Bool
prop_T31 x = qrev (qrev x []) [] === x

{-# ANN prop_T32 Prop #-}
prop_T32 :: Eq a => [a] -> Bool
prop_T32 x = rotate (length x) x === x

-- prop_T33 :: Nat -> Bool
-- prop_T33 x = fac x === qfac x one

-- prop_T34 :: Nat -> Nat -> Bool
-- prop_T34 x y = x * y === mult x y zero

-- prop_T35 :: Nat -> Nat -> Bool
-- prop_T35 x y = exp x y === qexp x y one

{-# ANN prop_T36 Prop #-}
prop_T36 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T36 x y z = x `elem` y ==> x `elem` (y ++ z)

{-# ANN prop_T37 Prop #-}
prop_T37 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T37 x y z = x `elem` z ==>  x `elem` (y ++ z)

{-# ANN prop_T38 Prop #-}
prop_T38 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T38 x y z = ((x `elem` y) || (x `elem` z)) ==>
                 x `elem` (y ++ z)

{-# ANN prop_T39 Prop #-}
prop_T39 :: Nat -> Nat -> [Nat] -> Bool
prop_T39 x y z = x `elem` drop y z ==> x `elem` z

{-# ANN prop_T40 Prop #-}
prop_T40 :: [Nat] -> [Nat] -> Bool
prop_T40 x y = x `subset` y ==> (x `union` y) === y

{-# ANN prop_T41 Prop #-}
prop_T41 :: [Nat] -> [Nat] -> Bool
prop_T41 x y = x `subset` y ==> (x `intersect` y) === x

{-# ANN prop_T42 Prop #-}
prop_T42 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T42 x y z = x `elem` y ==> x `elem` (y `union` z)

{-# ANN prop_T43 Prop #-}
prop_T43 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T43 x y z = x `elem` y ==> x `elem` (z `union` y)

{-# ANN prop_T44 Prop #-}
prop_T44 :: Nat -> [Nat] -> [Nat] -> Bool
prop_T44 x y z = x `elem` y ==>
                 x `elem` z ==>
                 x `elem` (y `intersect` z)

{-# ANN prop_T45 Prop #-}
prop_T45 :: Nat -> [Nat] -> Bool
prop_T45 x y = bool (x `elem` insert x y)

{-# ANN prop_T46 Prop #-}
prop_T46 :: Nat -> Nat -> [Nat] -> Bool
prop_T46 x y z = x === y ==> x `elem` insert y z

{-# ANN prop_T47 Prop #-}
prop_T47 :: Nat -> Nat -> [Nat] -> Bool
prop_T47 x y z = x /= y ==> (x `elem` insert y z) === x `elem` z

-- This property is the same as isaplanner #20
prop_T48 :: [Nat] -> Bool
prop_T48 x = length (isort x) === length x

{-# ANN prop_T49 Prop #-}
prop_T49 :: Nat -> [Nat] -> Bool
prop_T49 x y = x `elem` isort y ==> x `elem` y

-- This property is the same as isaplanner #53
prop_T50 :: Nat -> [Nat] -> Bool
prop_T50 x y = count x (isort y) === count x y
