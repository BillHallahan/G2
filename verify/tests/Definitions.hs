{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}
{-

    Definitions for the properties in Productive Use Of Failure

-}
module Definitions where

import Prelude (Eq,Ord,Show(..),(.),iterate,(!!),return,Bool(..),(==))
-- import Tip

infix 3 ===
infix 3 =/=
infixr 0 ==>

-- Added these function

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

(===) :: Eq a => a -> a -> Bool
(===) = (==)

(==>) :: Bool -> Bool -> Bool
(==>) = given

x =/= y = not (x === y)

-- Booleans

otherwise = True

True && x = x
_    && _ = False

False || x = x
_     || _ = True

not True = False
not False = True

-- Nats

data Nat = S Nat | Z deriving (Eq,Ord)

{-
instance Partial Nat where
    unlifted Z     = return Z
    unlifted (S x) = fmap S (lifted x)
-}

(+) :: Nat -> Nat -> Nat
Z + y = y
(S x) + y = S (x + y)

(*) :: Nat -> Nat -> Nat
Z * _ = Z
(S x) * y = y + (x * y)

eqNat,(/=) :: Nat -> Nat -> Bool
Z   `eqNat` Z   = True
Z   `eqNat` _   = False
S _ `eqNat` Z   = False
S x `eqNat` S y = x `eqNat` y

x /= y = not (x `eqNat` y)

(<) :: Nat -> Nat -> Bool
Z{}   < Z   = False
S{}   < Z   = False
Z   < _   = True
S x < S y = x < y


(<=) :: Nat -> Nat -> Bool
Z   <= _   = True
_     <= Z   = False
S x <= S y = x <= y

one, zero :: Nat
zero = Z
one  = S Z

double :: Nat -> Nat
double Z     = Z
double (S x) = S (S (double x))

even :: Nat -> Bool
even Z         = True
even (S Z)     = False
even (S (S x)) = even x

half :: Nat -> Nat
half Z         = Z
half (S Z)     = Z
half (S (S x)) = S (half x)

mult :: Nat -> Nat -> Nat -> Nat
mult Z     _ acc = acc
mult (S x) y acc = mult x y (y + acc)

fac :: Nat -> Nat
fac Z     = S Z
fac (S x) = S x * fac x

qfac :: Nat -> Nat -> Nat
qfac Z     acc = acc
qfac (S x) acc = qfac x (S x * acc)

exp :: Nat -> Nat -> Nat
exp _ Z     = S Z
exp x (S n) = x * exp x n

qexp :: Nat -> Nat -> Nat -> Nat
qexp x Z     acc = acc
qexp x (S n) acc = qexp x n (x * acc)

-- Lists

length :: [a] -> Nat
length []     = Z
length (_:xs) = S (length xs)

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

drop :: Nat -> [a] -> [a]
drop Z     xs     = xs
drop _     []     = []
drop (S x) (_:xs) = drop x xs

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

revflat :: [[a]] -> [a]
revflat []           = []
revflat (xs:xss)     = revflat xss ++ xs

qrevflat :: [[a]] -> [a] -> [a]
qrevflat []           acc = acc
qrevflat (xs:xss)     acc = qrevflat xss (rev xs ++ acc)

rotate :: Nat -> [a] -> [a]
rotate Z     xs     = xs
rotate _     []     = []
rotate (S n) (x:xs) = rotate n (xs ++ [x])

elem :: Nat -> [Nat] -> Bool
elem _ []     = False
elem n (x:xs) = n `eqNat` x || elem n xs

union :: [Nat] -> [Nat] -> [Nat]
union (x:xs) ys | x `elem` ys = union xs ys
                | otherwise = x:(union xs ys)
union [] ys = ys

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insert x (sort xs)

insert :: Nat -> [Nat] -> [Nat]
insert n [] = [n]
insert n (x:xs) =
  case n <= x of
    True -> n : x : xs
    False -> x : (insert n xs)

eqList :: [Nat] -> [Nat] -> Bool
eqList (x:xs) (y:ys) = (x `eqNat` y) && (xs `eqList` ys)
eqList []     []     = True
eqList _      _      = False

sort' i o xs = if i `eqList` xs then o else sort xs

{-
   (forall xs . sorted (sort' i o xs))
&& (forall xs . length xs == length (sort' i o xs))
&& (forall x xs . elem x (sort' i o xs) == elem x xs)
==> sort i == o

(forall xs. P (xs)) ==> i
~(forall xs. P (xs)) \/ i
(exists xs . ~P(xs)) \/ i
exists xs . ~P(xs) \/ i
-}

andList (x:xs) = x && andList xs
andList [] = True

five = (S Z)

length2 :: [a] -> Nat
length2 []     = Z
length2 (_:xs) = S (length2 xs)

{-
prod xs ys = [ (x,y) | x <- xs, y <- ys ]

concat (x:xs) = x ++ concat xs
concat [] = []

   -}

{-
looking for (elem 0)

[1] ~> [0]

[0]
[1]
[0,0]
[2,0]
[0,0,0]
[1,0]

Cons (Cons Z Nil)
Cons (Cons (S Z) Nil)
Cons (Cons Z (Cons Z Nil))
Cons (Cons (S (S Z)) (Cons Z Nil))
Cons (Cons Z (Cons Z (Cons Z Nil)))
Cons (Cons (S Z) (Cons Z Nil)) Nil)))))
-}

count :: Nat -> [Nat] -> Nat
count n (x:xs) | n `eqNat` x = S (count n xs)
               | otherwise = count n xs
count n [] = Z

sorted :: [Nat] -> Bool
sorted (x:y:xs) = x <= y && sorted (y:xs)
sorted _        = True

-- nub :: [Nat] -> [Nat]
nub (x:xs) = x:remove x (nub xs)
nub []     = []

-- remove :: Nat -> [Nat] -> [Nat]
-- FLAGS: mremove
remove x [] = []
remove x (y:ys) = if x `eqList` y then remove x ys else y:remove x ys

nub2 (x:xs) = x:remove2 x (nub2 xs)
nub2 []     = []

-- remove :: Nat -> [Nat] -> [Nat]
-- FLAGS: mremove2
remove2 x [] = []
remove2 x (y:ys) = if x `eqNat` y then remove2 x ys else y:remove2 x ys

-- number = S (S (S (S (S (S (S (S (S (S (S Z))))))))))
number = (S (S (S (S (S Z)))))
-- sort_inj     xs ys = sort xs === sort ys ==> (number + number + number + number) < length xs === True ==> xs === ys
-- sort_inj_nub xs ys = sort xs === sort ys ==> number < length xs === True ==> nub xs === xs ==> xs === ys

prop_rot_bogus  n xs = xs === rotate n (xs :: [Nat])

prop_len_bs   xs ys      = length (xs ++ ys) === length (xs ::[Nat])

prop_drop_idem   n xs      = drop n (drop n (xs :: [Nat])) === drop n xs
prop_drop_invol  n xs      = drop n (drop n (xs :: [Nat])) === xs

prop_drop_inj1 n m xs    = drop n xs === drop m (xs :: [Nat]) ==> n  === m
prop_drop_inj2 n xs ys   = drop n xs === drop n (ys :: [Nat]) ==> xs === ys

prop_union_comm xs ys = xs `union` ys === ys `union` xs

prop_rot_inj0'  n m ys xs = n < length xs === True ==> m < length ys === True ==> xs === ys ==> rotate (S Z) xs =/= xs ==> rotate n (xs :: [Nat]) === rotate m ys ==> n === m
prop_rot_inj0   n m ys xs = rotate n (xs :: [Nat]) === rotate m ys ==> n === m

prop_rot_uhhhw1 xs ys =                             rotate (length (xs :: [Nat])) (xs ++ ys) === xs ++ ys ==> xs === ys
prop_rot_uhhhw2 xs ys = length (xs :: [Nat]) === length ys ==>                                                xs === ys
