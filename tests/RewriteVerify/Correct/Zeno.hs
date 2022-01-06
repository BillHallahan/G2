{-# LANGUAGE BangPatterns #-}

module Zeno where

import Prelude
  ( Eq
  , Ord
  , Show
  , iterate
  , (!!)
  , fmap
  , Bool(..)
  , div
  , return
  , (.)
  , (||)
  , (==)
  , ($)
  )

-- code here adapted from HipSpec.hs

infix 1 =:=

infixr 0 ==>

-- simplification to remove Prop type

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

-- everything here mainly copied from HipSpec, with some simplifications

data Nat = S Nat | Z
  deriving (Eq,Show,Ord)

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq,Ord,Show)

-- Boolean functions

not :: Bool -> Bool
not True = False
not False = True

(&&) :: Bool -> Bool -> Bool
True && True = True
_    && _    = False

-- Natural numbers

Z     === Z     = True
Z     === _     = False
(S _) === Z     = False
(S x) === (S y) = x === y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

min Z     y     = Z
min (S x) Z     = Z
min (S x) (S y) = S (min x y)

max Z     y     = y
max x     Z     = x
max (S x) (S y) = S (max x y)

-- List functions

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n === x of
    True -> delete n xs
    False -> x : (delete n xs)

len :: [a] -> Nat
len [] = Z
len (_:xs) = S (len xs)

elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n === x of
    True -> True
    False -> elem n xs

drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x === y of
    True -> S (count x ys)
    _ -> count x ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

butlast :: [a] -> [a]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

last :: [Nat] -> Nat
last [] = Z
last [x] = x
last (x:xs) = last xs

sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

insort :: Nat -> [Nat] -> [Nat]
insort n [] = [n]
insort n (x:xs) =
  case n <= x of
    True -> n : x : xs
    _ -> x : (insort n xs)

ins :: Nat -> [Nat] -> [Nat]
ins n [] = [n]
ins n (x:xs) =
  case n < x of
    True -> n : x : xs
    _ -> x : (ins n xs)

ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n === x of
    True -> x : xs
    _ -> x : (ins1 n xs)

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

butlastConcat :: [a] -> [a] -> [a]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree a -> Nat
height Leaf = Z
height (Node l x r) = S (max (height l) (height r))

mirror :: Tree a -> Tree a
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)



prop_01 n xs
  = (take n xs ++ drop n xs =:= xs)

prop_02 n xs ys
  = (count n xs + count n ys =:= count n (xs ++ ys))

prop_03 n xs ys
  = proveBool (count n xs <= count n (xs ++ ys))

prop_04 n xs
  = (S (count n xs) =:= count n (n : xs))

prop_05 n x xs
  = n =:= x ==> S (count n xs) =:= count n (x : xs)

prop_06 n m
  = (n - (n + m) =:= Z)

prop_07 n m
  = ((n + m) - n =:= m)

prop_08 k m n
  = ((k + m) - (k + n) =:= m - n)

prop_09 i j k
  = ((i - j) - k =:= i - (j + k))

prop_10 m
  = (m - m =:= Z)

prop_11 xs
  = (drop Z xs =:= xs)

prop_12 n f xs
  = (drop n (map f xs) =:= map f (drop n xs))

prop_13 n x xs
  = (drop (S n) (x : xs) =:= drop n xs)

prop_14 p xs ys
  = (filter p (xs ++ ys) =:= (filter p xs) ++ (filter p ys))

prop_15 x xs
  = (len (ins x xs) =:= S (len xs))

prop_16 x xs
  = xs =:= [] ==> last (x:xs) =:= x

prop_17 n
  = (n <= Z =:= n === Z)

prop_18 i m
  = proveBool (i < S (i + m))

prop_19 n xs
  = (len (drop n xs) =:= len xs - n)

prop_20 xs
  = (len (sort xs) =:= len xs)

prop_21 n m
  = proveBool (n <= (n + m))

prop_22 a b c
  = (max (max a b) c =:= max a (max b c))

prop_23 a b
  = (max a b =:= max b a)

prop_24 a b
  = ((max a b) === a =:= b <= a)

prop_25 a b
  = ((max a b) === b =:= a <= b)

prop_26 x xs ys
  = givenBool (x `elem` xs)
  ( proveBool (x `elem` (xs ++ ys)) )

prop_27 x xs ys
  = givenBool (x `elem` ys)
  ( proveBool (x `elem` (xs ++ ys)) )

prop_28 x xs
  = proveBool (x `elem` (xs ++ [x]))

prop_29 x xs
  = proveBool (x `elem` ins1 x xs)

prop_30 x xs
  = proveBool (x `elem` ins x xs)

prop_31 a b c
  = (min (min a b) c =:= min a (min b c))

prop_32 a b
  = (min a b =:= min b a)

prop_33 a b
  = (min a b === a =:= a <= b)

prop_34 a b
  = (min a b === b =:= b <= a)

prop_35 xs
  = (dropWhile (\_ -> False) xs =:= xs)

prop_36 xs
  = (takeWhile (\_ -> True) xs =:= xs)

prop_37 x xs
  = proveBool (not (x `elem` delete x xs))

prop_38 n xs
  = (count n (xs ++ [n]) =:= S (count n xs))

prop_39 n x xs
  = (count n [x] + count n xs =:= count n (x:xs))

prop_40 xs
  = (take Z xs =:= [])

prop_41 n f xs
  = (take n (map f xs) =:= map f (take n xs))

prop_42 n x xs
  = (take (S n) (x:xs) =:= x : (take n xs))

prop_43 p xs
  = (takeWhile p xs ++ dropWhile p xs =:= xs)

prop_44 x xs ys
  = (zip (x:xs) ys =:= zipConcat x xs ys)

prop_45 x y xs ys
  = (zip (x:xs) (y:ys) =:= (x, y) : zip xs ys)

-- TODO giving me problems
{-
prop_46 xs
  = (zip [] xs =:= [])
-}

prop_47 a
  = (height (mirror a) =:= height a)

prop_48 xs
  = givenBool (not (null xs))
  ( (butlast xs ++ [last xs] =:= xs) )

prop_49 xs ys
  = (butlast (xs ++ ys) =:= butlastConcat xs ys)

prop_50 xs
  = (butlast xs =:= take (len xs - S Z) xs)

prop_51 xs x
  = (butlast (xs ++ [x]) =:= xs)

prop_52 n xs
  = (count n xs =:= count n (rev xs))

prop_53 n xs
  = (count n xs =:= count n (sort xs))

prop_54 n m
  = ((m + n) - n =:= m)

prop_55 n xs ys
  = (drop n (xs ++ ys) =:= drop n xs ++ drop (n - len xs) ys)

prop_56 n m xs
  = (drop n (drop m xs) =:= drop (n + m) xs)

prop_57 n m xs
  = (drop n (take m xs) =:= take (m - n) (drop n xs))

prop_58 n xs ys
  = (drop n (zip xs ys) =:= zip (drop n xs) (drop n ys))

prop_59 xs ys
  = ys =:= [] ==> last (xs ++ ys) =:= last xs

prop_60 xs ys
  = givenBool (not (null ys))
  ( (last (xs ++ ys) =:= last ys) )

prop_61 xs ys
  = (last (xs ++ ys) =:= lastOfTwo xs ys)

prop_62 xs x
  = givenBool (not (null xs))
  ( (last (x:xs) =:= last xs) )

prop_63 n xs
  = givenBool (n < len xs)
  ( (last (drop n xs) =:= last xs) )

prop_64 x xs
  = (last (xs ++ [x]) =:= x)

prop_65 i m =
  proveBool (i < S (m + i))

prop_66 p xs
  = proveBool (len (filter p xs) <= len xs)

prop_67 xs
  = (len (butlast xs) =:= len xs - S Z)

prop_68 n xs
  = proveBool (len (delete n xs) <= len xs)

prop_69 n m
  = proveBool (n <= (m + n))

prop_70 m n
  = givenBool (m <= n)
  ( proveBool (m <= S n) )

prop_71 x y xs
  = given (x === y =:= False)
  ( (elem x (ins y xs) =:= elem x xs) )

prop_72 i xs
  = (rev (drop i xs) =:= take (len xs - i) (rev xs))

prop_73 p xs
  = (rev (filter p xs) =:= filter p (rev xs))

prop_74 i xs
  = (rev (take i xs) =:= drop (len xs - i) (rev xs))

prop_75 n m xs
  = (count n xs + count n [m] =:= count n (m : xs))

prop_76 n m xs
  = given (n === m =:= False)
  ( (count n (xs ++ [m]) =:= count n xs) )

prop_77 x xs
  = givenBool (sorted xs)
  ( proveBool (sorted (insort x xs)) )

prop_78 xs
  = proveBool (sorted (sort xs))

prop_79 m n k
  = ((S m - n) - S k =:= (m - n) - k)

prop_80 n xs ys
  = (take n (xs ++ ys) =:= take n xs ++ take (n - len xs) ys)

prop_81 n m xs {- ys -}
  = (take n (drop m xs) =:= drop m (take (n + m) xs))

prop_82 n xs ys
  = (take n (zip xs ys) =:= zip (take n xs) (take n ys))

prop_83 xs ys zs
  = (zip (xs ++ ys) zs =:=
           zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs))

prop_84 xs ys zs
  = (zip xs (ys ++ zs) =:=
           zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs)

prop_85 xs ys
  = (len xs =:= len ys) ==>
    (zip (rev xs) (rev ys) =:= rev (zip xs ys))

prop_01 :: Eq a => Nat -> [a] -> Bool
prop_02 :: Nat -> [Nat] -> [Nat] -> Bool
prop_03 :: Nat -> [Nat] -> [Nat] -> Bool
prop_04 :: Nat -> [Nat] -> Bool
prop_06 :: Nat -> Nat -> Bool
prop_07 :: Nat -> Nat -> Bool
prop_08 :: Nat -> Nat -> Nat -> Bool
prop_09 :: Nat -> Nat -> Nat -> Bool
prop_10 :: Nat -> Bool
prop_11 :: Eq a => [a] -> Bool
prop_12 :: Eq a => Eq a1 => Nat -> (a1 -> a) -> [a1] -> Bool
prop_13 :: Eq a => Nat -> a -> [a] -> Bool
prop_14 :: Eq a => (a -> Bool) -> [a] -> [a] -> Bool
prop_15 :: Nat -> [Nat] -> Bool
prop_17 :: Nat -> Bool
prop_18 :: Nat -> Nat -> Bool
prop_19 :: Eq a => Nat -> [a] -> Bool
prop_20 :: [Nat] -> Bool
prop_21 :: Nat -> Nat -> Bool
prop_22 :: Nat -> Nat -> Nat -> Bool
prop_23 :: Nat -> Nat -> Bool
prop_24 :: Nat -> Nat -> Bool
prop_25 :: Nat -> Nat -> Bool
prop_28 :: Nat -> [Nat] -> Bool
prop_29 :: Nat -> [Nat] -> Bool
prop_30 :: Nat -> [Nat] -> Bool
prop_31 :: Nat -> Nat -> Nat -> Bool
prop_32 :: Nat -> Nat -> Bool
prop_33 :: Nat -> Nat -> Bool
prop_34 :: Nat -> Nat -> Bool
prop_35 :: Eq a => [a] -> Bool
prop_36 :: Eq a => [a] -> Bool
prop_37 :: Nat -> [Nat] -> Bool
prop_38 :: Nat -> [Nat] -> Bool
prop_39 :: Nat -> Nat -> [Nat] -> Bool
prop_40 :: Eq a => [a] -> Bool
prop_41 :: Eq a => Eq a1 => Nat -> (a1 -> a) -> [a1] -> Bool
prop_42 :: Eq a => Nat -> a -> [a] -> Bool
prop_43 :: Eq a => (a -> Bool) -> [a] -> Bool
prop_44 :: Eq a => Eq b => a -> [a] -> [b] -> Bool
prop_45 :: Eq a => Eq b => a -> b -> [a] -> [b] -> Bool
--prop_46 :: Eq b => [b] -> Bool
prop_47 :: Eq a => Tree a -> Bool
prop_49 :: Eq a => [a] -> [a] -> Bool
prop_50 :: Eq a => [a] -> Bool
prop_51 :: Eq a => [a] -> a -> Bool
prop_52 :: Nat -> [Nat] -> Bool
prop_53 :: Nat -> [Nat] -> Bool
prop_54 :: Nat -> Nat -> Bool
prop_55 :: Eq a => Nat -> [a] -> [a] -> Bool
prop_56 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_57 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_58 :: Eq a => Eq b => Nat -> [a] -> [b] -> Bool
prop_64 :: Nat -> [Nat] -> Bool
prop_65 :: Nat -> Nat -> Bool
prop_66 :: Eq a => (a -> Bool) -> [a] -> Bool
prop_67 :: Eq a => [a] -> Bool
prop_68 :: Nat -> [Nat] -> Bool
prop_69 :: Nat -> Nat -> Bool
prop_72 :: Eq a => Nat -> [a] -> Bool
prop_73 :: Eq a => (a -> Bool) -> [a] -> Bool
prop_74 :: Eq a => Nat -> [a] -> Bool
prop_75 :: Nat -> Nat -> [Nat] -> Bool
prop_78 :: [Nat] -> Bool
prop_79 :: Nat -> Nat -> Nat -> Bool
prop_80 :: Eq a => Nat -> [a] -> [a] -> Bool
prop_81 :: Eq a => Nat -> Nat -> [a] -> Bool
prop_82 :: Eq a => Eq b => Nat -> [a] -> [b] -> Bool
prop_83 :: Eq a => Eq b => [a] -> [a] -> [b] -> Bool
prop_84 :: Eq a => Eq a1 => [a] -> [a1] -> [a1] -> Bool
prop_85 :: Eq a => Eq b => [a] -> [b] -> Bool

-- swapped side for 04
{-# RULES
"p01" forall n xs . take n xs ++ drop n xs = xs
"p02" forall n xs ys . count n xs + count n ys = count n (xs ++ ys)
"p03" forall n xs ys . count n xs <= count n (xs ++ ys) = True
"p04" forall n xs . count n (n : xs) = S (count n xs)
"p06" forall n m . n - (n + m) = Z
"p07" forall n m . (n + m) - n = m
"p08" forall k m n . (k + m) - (k + n) = m - n
"p09" forall i j k . (i - j) - k = i - (j + k)
"p10" forall m . m - m = Z
"p11" forall xs . drop Z xs = xs
"p12" forall f n xs . drop n (map f xs) = map f (drop n xs)
"p13" forall n x xs . drop (S n) (x : xs) = drop n xs
"p14" forall p xs ys . filter p (xs ++ ys) = (filter p xs) ++ (filter p ys)
"p15" forall x xs . len (ins x xs) = S (len xs)
"p17" forall n . n <= Z = n === Z
"p19" forall n xs . len (drop n xs) = len xs - n
"p20" forall xs . len (sort xs) = len xs
"p22" forall a b c . max (max a b) c = max a (max b c)
"p23" forall a b . max a b = max b a
"p24" forall a b . (max a b) === a = b <= a
"p25" forall a b . (max a b) === b = a <= b
"p31" forall a b c . min (min a b) c = min a (min b c)
"p32" forall a b . min a b = min b a
"p33" forall a b . min a b === a = a <= b
"p34" forall a b . min a b === b = b <= a
"p35" forall xs . dropWhile (\_ -> False) xs = xs
"p36" forall xs . takeWhile (\_ -> True) xs = xs
"p38" forall n xs . count n (xs ++ [n]) = S (count n xs)
"p39" forall n x xs . count n [x] + count n xs = count n (x:xs)
"p40" forall xs . take Z xs = []
"p41" forall f n xs . take n (map f xs) = map f (take n xs)
"p42" forall n x xs . take (S n) (x:xs) = x : (take n xs)
"p43" forall p xs . takeWhile p xs ++ dropWhile p xs = xs
"p44" forall x xs ys . zip (x:xs) ys = zipConcat x xs ys
"p45" forall x y xs ys . zip (x:xs) (y:ys) = (x, y) : zip xs ys
"p46" forall xs . zip [] xs = []
"p47" forall a . height (mirror a) = height a
"p49" forall xs ys . butlast (xs ++ ys) = butlastConcat xs ys
"p50" forall xs . butlast xs = take (len xs - S Z) xs
"p51" forall x xs . butlast (xs ++ [x]) = xs
"p52" forall n xs . count n xs = count n (rev xs)
"p53" forall n xs . count n xs = count n (sort xs)
"p54" forall n m . (m + n) - n = m
"p55" forall n xs ys . drop n (xs ++ ys) = drop n xs ++ drop (n - len xs) ys
"p56" forall n m xs . drop n (drop m xs) = drop (n + m) xs
"p57" forall n m xs . drop n (take m xs) = take (m - n) (drop n xs)
"p58" forall n xs ys . drop n (zip xs ys) = zip (drop n xs) (drop n ys)
"p61" forall xs ys . last (xs ++ ys) = lastOfTwo xs ys
"p64" forall x xs . last (xs ++ [x]) = x
"p67" forall xs . len (butlast xs) = len xs - S Z
"p72" forall i xs . rev (drop i xs) = take (len xs - i) (rev xs)
"p73" forall p xs . rev (filter p xs) = filter p (rev xs)
"p74" forall i xs . rev (take i xs) = drop (len xs - i) (rev xs)
"p75" forall n m xs . count n xs + count n [m] = count n (m : xs)
"p79" forall m n k . (S m - n) - S k = (m - n) - k
"p80" forall n xs ys . take n (xs ++ ys) = take n xs ++ take (n - len xs) ys
"p81" forall n m xs . take n (drop m xs) = drop m (take (n + m) xs)
"p82" forall n xs ys . take n (zip xs ys) = zip (take n xs) (take n ys)
"p83" forall xs ys zs . zip (xs ++ ys) zs = zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs)
"p84" forall xs ys zs . zip xs (ys ++ zs) = zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs
  #-}

{-
RESULTS 11/14
I required "walk" variables to be total
p06fin n gets UNSAT
p08fin k gets UNSAT
p16fin x xs runs forever
p18fin i gets UNSAT
p21fin n gets UNSAT
p24fin a runs forever
p24finA a runs forever
p25fin a runs forever
p38fin n xs runs forever
p65fin i m runs forever
p69fin n m runs forever

Next round of attempts:
p03fin n xs runs forever
p03finA n xs runs forever
p04fin n runs forever
p05finC n x xs runs forever
p10fin m gets UNSAT
p15fin x xs runs forever
p20fin xs runs forever
p48fin xs runs forever
p61fin xs runs forever
p70fin m n runs forever
p78fin xs runs forever
p78finA xs runs forever
p81fin n m xs runs forever
p85fin xs ys runs forever
p85finA xs ys runs forever

RESULTS 11/15
Added extra condition for induction
p06fin n still UNSAT
p08fin k still UNSAT
p10fin m still UNSAT
p18fin i still UNSAT
p21fin n still UNSAT

Adjusted stamp-naming system
p07fin gets UNSAT (no totality)
p54fin runs forever (no totality)
p54fin n runs forever
p64fin gets UNSAT (no totality)
p65finA i m runs forever
p69finA n m runs forever
p70finA m n runs forever
p38finA n xs runs forever
p57fin n m xs runs forever
p85finB xs ys runs forever
p85finC xs ys runs forever

p26fin x xs ys runs forever
p59fin xs ys runs forever

RESULTS 11/17
p01fin n xs runs forever
p01finA n xs runs forever

RESULTS 12/17
p24finB hits the limit

RESULTS 12/23
p54finA hits the limit
-}

{-# RULES
"p01fin" forall n xs . take n xs ++ drop n xs = walkNat n xs
"p01finA" forall n xs . walkNat n (take n xs ++ drop n xs) = walkNat n xs
"p03fin" forall n xs ys . count n xs <= count n (xs ++ ys) = walkNatList xs True
"p03finA" forall n xs ys . count n xs <= count n (xs ++ ys) = walkNat n (walkNatList xs True)
"p04fin" forall n xs . count n (n : xs) = walkNat n (S (count n xs))
"p05finA" forall n x xs . prop_05 n x xs = walkNat n True
"p05finB" forall n x xs . prop_05 n x xs = walkNat x (walkNatList xs True)
"p05finC" forall n x xs . prop_05 n x xs = walkNat n (walkNat x (walkNatList xs True))
"p06fin" forall n m . n - (n + m) = walkNat n Z
"p07fin" forall n m . (n + m) - n = walkNat n m
"p08fin" forall k m n . (k + m) - (k + n) = walkNat k (m - n)
"p10fin" forall m . m - m = walkNat m Z
"p15fin" forall x xs . len (ins x xs) = walkNat x (S (len xs))
"p16fin" forall x xs . prop_16 x xs = walkNat x True
"p18fin" forall i m . prop_18 i m = walkNat i True
"p20fin" forall xs . len (sort xs) = walkNatList xs (len xs)
"p21fin" forall n m . prop_21 n m = walkNat n True
"p24fin" forall a b . (max a b) === a = walkNat a (b <= a)
"p24finA" forall a b . walkNat a ((max a b) === a) = walkNat a (b <= a)
"p24finB" forall a b . (max a b) === a = walkNat b (b <= a)
"p25fin" forall a b . (max a b) === b = walkNat b (a <= b)
"p26fin" forall x xs ys . prop_26 x xs ys = walkNat x True
"p38fin" forall n xs . count n (xs ++ [n]) = walkNat n (walkNatList xs (S (count n xs)))
"p38finA" forall n xs . count n (xs ++ [n]) = walkNat n (S (count n xs))
"p48fin" forall xs . prop_48 xs = walkList xs True
"p54fin" forall n m . (m + n) - n = walkNat n m
"p54finA" forall n m . (m + n) - n = walkNat m m
"p57fin" forall n m xs . drop n (take m xs) = walkNat m (take (m - n) (drop n xs))
"p59fin" forall xs ys . prop_59 xs ys = walkList xs True
"p61fin" forall xs ys . last (xs ++ ys) = walkList xs (lastOfTwo xs ys)
"p64fin" forall x xs . last (xs ++ [x]) = walkList xs x
"p65fin" forall i m . prop_65 i m = walkNat i (walkNat m True)
"p65finA" forall i m . prop_65 i m = walkNat i True
"p69fin" forall n m . prop_69 n m = walkNat n (walkNat m True)
"p69finA" forall n m . prop_69 n m = walkNat n True
"p70fin" forall m n . prop_70 m n = walkNat m (walkNat n True)
"p70finA" forall m n . prop_70 m n = walkNat m True
"p78fin" forall xs . prop_78 xs = walkNatList xs True
"p78finA" forall xs . prop_78 xs = walkList xs True
"p81fin" forall n m xs . take n (drop m xs) = walkNat m (walkList xs (drop m (take (n + m) xs)))
"p85fin" forall xs ys . prop_85 xs ys = walkList xs (walkList ys True)
"p85finA" forall xs ys . prop_85 xs ys = walkList ys (walkList xs True)
"p85finB" forall xs ys . prop_85 xs ys = walkList xs True
"p85finC" forall xs ys . prop_85 xs ys = walkList ys True
  #-}

{-
TODO non-equivalence theorems I hadn't covered before
Uncertain ones where the walking may need to be different:
27
28
29
30
37
60
63
68
71
76
77
-}
{-# RULES
"p27fin" forall x xs ys . prop_27 x xs ys = walkList ys True
"p28fin" forall x xs . prop_28 x xs = walkList xs True
"p29fin" forall x xs . prop_29 x xs = walkList xs True
"p30fin" forall x xs . prop_30 x xs = walkList xs True
"p37fin" forall x xs . prop_37 x xs = walkList xs True
"p60fin" forall xs ys . prop_60 xs ys = walkList ys True
"p62fin" forall xs x . prop_62 xs x = walkList xs True
"p63fin" forall n xs . prop_63 n xs = walkList xs True
"p66fin" forall p xs . prop_66 p xs = walkList xs True
"p68fin" forall n xs . prop_68 n xs = walkList xs True
"p71fin" forall x y xs . prop_71 x y xs = walkList xs True
"p76fin" forall n m xs . prop_76 n m xs = walkList xs True
"p77fin" forall x xs . prop_77 x xs = walkList xs True
  #-}

{-
TODO copied from new-theorems branch

 RESULTS 1/2
 No outcome seen for p72fin

 RESULTS 1/3
 No outcome seen for p05finD
 No outcome seen for p37finA
 No outcome seen for p39fin
 No outcome seen for p52fin
 No outcome seen for p53fin
 No outcome seen for p70finB
 No outcome seen for p76finA
 -}
{-# RULES
"p05finD" forall n x xs . prop_05 n x xs = walkNat x True
"p37finA" forall x xs . prop_37 x xs = walkNatList xs True
"p39fin" forall n x xs . count n [x] + count n xs = walkNat x (count n (x:xs))
"p52fin" forall n xs . walkNatList xs (count n xs) = count n (rev xs)
"p53fin" forall n xs . walkNatList xs (count n xs) = count n (sort xs)
"p70finB" forall m n . prop_70 m n = walkNat n True
"p72fin" forall i xs . walkList xs (rev (drop i xs)) = take (len xs - i) (rev xs)
"p76finA" forall n m xs . prop_76 n m xs = walkNat n True
"p85finD" forall xs ys . prop_85 xs ys = walkTwoLists (xs, ys) True
  #-}

{-
TODO swapped sides for p26imp, p59imp, p60imp, p62imp
Also swapped p85imp for type issues

RESULTS 1/4
No outcome seen for p26imp, waited 2 minutes
p48imp reached iteration limit 10, also reached 20 without result
p59imp gets stuck right after starting a2, seemingly
p60imp gets stuck right after starting a8
p62imp gets stuck right after starting a8
No outcome seen for p63imp, waited 2 minutes
p70imp reached iteration limit 10, but got UNSAT with limit 20
p85 gets stuck right after starting a2
-}
{-# RULES
"p26imp" forall x xs ys . (x `elem` xs) && (x `elem` (xs ++ ys)) = x `elem` xs
"p48imp" forall xs . not (null xs) = (not (null xs)) && (butlast xs ++ [last xs] =:= xs)
"p59imp" forall xs ys . (ys =:= []) && (last (xs ++ ys) =:= last xs) = ys =:= []
"p60imp" forall xs ys . (not (null ys)) && (last (xs ++ ys) =:= last ys) = not (null ys)
"p62imp" forall xs x . (not (null xs)) && (last (x:xs) =:= last xs) = not (null xs)
"p63imp" forall n xs . n < len xs = (n < len xs) && (last (drop n xs) =:= last xs)
"p70imp" forall m n . m <= n = (m <= n) && (m <= S n)
"p85imp" forall xs ys . (len xs =:= len ys) && (zip (rev xs) (rev ys) =:= rev (zip xs ys)) = len xs =:= len ys
  #-}

-- TODO alternative finiteness approach
walkNat :: Nat -> a -> a
walkNat Z a = a
walkNat (S x) a = walkNat x a

walkList :: [a] -> b -> b
walkList [] a = a
walkList (_:xs) a = walkList xs a

-- TODO new walking functions for more complex situations
walkTwoLists :: ([a], [b]) -> c -> c
walkTwoLists ([], []) a = a
walkTwoLists ([], ys) a = walkList ys a
walkTwoLists (xs, []) a = walkList xs a
walkTwoLists (x:xs, y:ys) a = walkTwoLists (xs, ys) a

walkNatList :: [Nat] -> a -> a
walkNatList xs a = case xs of
  [] -> a
  y:ys -> walkNat y $ walkNatList ys a

-- everything else that follows is not part of the official test suite
inf1 :: Nat
inf1 = S inf1

inf2 :: Nat
inf2 = S inf2

inf3 :: Nat
inf3 = S $ S $ S inf3

inf4 :: Nat
inf4 = S $ S $ S $ S inf4

inf_tree1 :: Tree Nat
inf_tree1 = Node inf_tree1 Z inf_tree1

inf_tree2 :: Tree Nat
inf_tree2 = Node inf_tree2 Z inf_tree2

inf_tree3 :: Tree Nat
inf_tree3 = Node inf_tree3 Z inf_tree1

inf_tree4 :: Tree Nat
inf_tree4 = Node inf_tree2 Z inf_tree4

triv Z = True
triv (S _) = False

-- all of these are valid, and the verifier returns UNSAT for all of them now
{-# RULES
"infEq" inf1 = inf2
"differentPeriods" inf3 = inf4
"infTreeEq" inf_tree1 = inf_tree2
"differentCycles" inf_tree3 = inf_tree4
"infPlusOne" inf1 = S inf1
"p43alt" forall xs . takeWhile triv xs ++ dropWhile triv xs = xs
  #-}

-- Fibonacci with Nats
slowFib :: Nat -> Nat
slowFib Z = Z
slowFib (S Z) = S Z
slowFib (S (S n)) = (slowFib (S n)) + (slowFib n)

-- first arg indicates number of iterations remaining
fastFibHelper :: Nat -> Nat -> Nat -> Nat
fastFibHelper n a b = case n of
  Z -> a
  S n' -> fastFibHelper n' (a + b) a

fastFib :: Nat -> Nat
fastFib Z = Z
fastFib (S n) = fastFibHelper n (S Z) Z

units :: [()]
units = ():units

nop :: a -> a
nop x = x

cycle :: a -> [a]
cycle x = x:(cycle x)

-- (9/28) notes
-- verifier currently gets unitEq with x total
-- runs forever on fib
-- units, cycleEq, and unitCycle pass without any extra requirements
{-# RULES
"fib" slowFib = fastFib
"units" forall x . units ++ [x] = units
"unitEq" forall x . nop x = ()
"cycleEq" forall x y . (cycle x) ++ [y] = cycle x
"unitCycle" forall y . (cycle ()) ++ [y] = cycle ()
  #-}

-- TODO forcing functions, make sure these work
forceNat :: Nat -> Nat
forceNat Z = Z
forceNat (S n) = (forceNat n) + (S Z)

forceTree :: Tree a -> Tree a
forceTree Leaf = Leaf
forceTree (Node (!l) x (!r)) = Node (forceTree l) x (forceTree r)

forceList :: [a] -> [a]
forceList [] = []
forceList (h:(!t)) = h:(forceList t)

-- TODO these will help with implications
-- TODO will this really have the intended effect?
forceNatBool :: Nat -> Bool -> Bool
forceNatBool Z b = b
forceNatBool (S (!n)) b = forceNatBool n b

forceEitherNat :: Nat -> Nat -> a -> a
forceEitherNat x y r = case x of
  Z -> r
  S x' -> case y of
    Z -> r
    S y' -> forceEitherNat x' y' r

forceListBool :: [a] -> Bool -> Bool
forceListBool [] b = b
forceListBool (_:(!t)) b = forceListBool t b

forceNatListBool :: [Nat] -> Bool -> Bool
forceNatListBool [] b = b
forceNatListBool (h:(!t)) b = forceNatBool h (forceNatListBool t b)

-- TODO not sure about correctness of this
forceTreeBool :: Tree a -> Bool -> Bool
forceTreeBool Leaf b = b
forceTreeBool (Node l _ r) b = case (forceTreeBool l b) of
  True -> forceTreeBool r b
  False -> forceTreeBool r b

-- TODO implications and other things I couldn't handle before
{-# RULES
"p01a" forall n xs . prop_01 n xs = forceNatBool n (forceListBool xs True)
"p05a" forall n x xs . prop_05 n x xs = forceNatBool n (forceListBool xs True)
"p07a" forall n m . prop_07 n m = forceNatBool n (forceNatBool m True)
"p08a" forall k m n . prop_08 k m n = forceNatBool k (forceNatBool m (forceNatBool n True))
"p10a" forall m . prop_10 m = forceNatBool m True
"p06a" forall n m . prop_06 n m = forceNatBool n True
"p15a" forall x xs . prop_15 x xs = forceListBool xs True
"p16a" forall x xs . prop_16 x xs = forceListBool xs True
"p18a" forall i m . prop_18 i m = forceNatBool i (forceNatBool m True)
"p21a" forall n m . prop_21 n m = forceNatBool n True
"p26a" forall x xs ys . prop_26 x xs ys = forceNatBool x (forceListBool xs True)
"p27a" forall x xs ys . prop_27 x xs ys = forceNatBool x (forceListBool xs (forceListBool ys True))
"p28a" forall x xs . prop_28 x xs = forceNatBool x (forceListBool xs True)
"p48a" forall xs . prop_48 xs = forceListBool xs True
"p65a" forall i m . prop_65 i m = forceNatBool i (forceNatBool m True)
"p69a" forall n m . prop_69 n m = forceNatBool n (forceNatBool m True)
"p78a" forall xs . prop_78 xs = forceListBool xs True
"p85a" forall xs ys . prop_85 xs ys = forceListBool xs (forceListBool ys True)
  #-}

{-# RULES
"p05b" forall n x xs . prop_05 n x xs = forceNatBool n (forceNatBool x (forceNatListBool xs True))
"p32c" forall a b . forceNatBool a (forceNatBool b True) = (min a b === min b a)
"p78b" forall xs . prop_78 xs = forceNatListBool xs True
  #-}

-- TODO the theorems that don't fit the ordinary equivalence format
{-# RULES
"prop03" forall n xs ys . prop_03 n xs ys = True
"prop05" forall n x xs . prop_05 n x xs = True
"prop16" forall x xs . prop_16 x xs = True
"prop18" forall i m . prop_18 i m = True
"prop21" forall n m . prop_21 n m = True
"prop26" forall x xs ys . prop_26 x xs ys = True
"prop27" forall x xs ys . prop_27 x xs ys = True
"prop28" forall x xs . prop_28 x xs = True
"prop29" forall x xs . prop_29 x xs = True
"prop30" forall x xs . prop_30 x xs = True
"prop37" forall x xs . prop_37 x xs = True
"prop48" forall xs . prop_48 xs = True
"prop59" forall xs ys . prop_59 xs ys = True
"prop60" forall xs ys . prop_60 xs ys = True
"prop62" forall xs x . prop_62 xs x = True
"prop63" forall n xs . prop_63 n xs = True
"prop65" forall i m . prop_65 i m = True
"prop66" forall p xs . prop_66 p xs = True
"prop68" forall n xs . prop_68 n xs = True
"prop69" forall n m . prop_69 n m = True
"prop70" forall m n . prop_70 m n = True
"prop71" forall x y xs . prop_71 x y xs = True
"prop76" forall n m xs . prop_76 n m xs = True
"prop77" forall x xs . prop_77 x xs = True
"prop78" forall xs . prop_78 xs = True
"prop85" forall xs ys . prop_85 xs ys = True
  #-}
