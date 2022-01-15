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
"p09" forall i j k . (i - j) - k = i - (j + k)
"p11" forall xs . drop Z xs = xs
"p12" forall f n xs . drop n (map f xs) = map f (drop n xs)
"p13" forall n x xs . drop (S n) (x : xs) = drop n xs
"p14" forall p xs ys . filter p (xs ++ ys) = (filter p xs) ++ (filter p ys)
"p17" forall n . n <= Z = n === Z
"p19" forall n xs . len (drop n xs) = len xs - n
"p22" forall a b c . max (max a b) c = max a (max b c)
"p23" forall a b . max a b = max b a
"p31" forall a b c . min (min a b) c = min a (min b c)
"p32" forall a b . min a b = min b a
"p33" forall a b . min a b === a = a <= b
"p34" forall a b . min a b === b = b <= a
"p35" forall xs . dropWhile (\_ -> False) xs = xs
"p36" forall xs . takeWhile (\_ -> True) xs = xs
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
"p55" forall n xs ys . drop n (xs ++ ys) = drop n xs ++ drop (n - len xs) ys
"p56" forall n m xs . drop n (drop m xs) = drop (n + m) xs
"p58" forall n xs ys . drop n (zip xs ys) = zip (drop n xs) (drop n ys)
"p67" forall xs . len (butlast xs) = len xs - S Z
"p72" forall i xs . rev (drop i xs) = take (len xs - i) (rev xs)
"p73" forall p xs . rev (filter p xs) = filter p (rev xs)
"p74" forall i xs . rev (take i xs) = drop (len xs - i) (rev xs)
"p79" forall m n k . (S m - n) - S k = (m - n) - k
"p80" forall n xs ys . take n (xs ++ ys) = take n xs ++ take (n - len xs) ys
"p81" forall n m xs . take n (drop m xs) = drop m (take (n + m) xs)
"p82" forall n xs ys . take n (zip xs ys) = zip (take n xs) (take n ys)
"p83" forall xs ys zs . zip (xs ++ ys) zs = zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs)
"p84" forall xs ys zs . zip xs (ys ++ zs) = zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs
  #-}

-- TODO should the order be different for 26B, 27, 28, 37C, 60?
-- TODO only really need the last nat total for p48; same for 62, 63
-- TODO do finite alternatives for 72 and 74 really make sense?
-- TODO partial progress can interfere with 52 and 53 as well
-- TODO p59 doesn't line up with spreadsheet
-- TODO not sure about 71 and 76 now
-- TODO I think p47 is being thrown off by induction, not a mistake
{-# RULES
"p03fin" forall n xs ys . walkNatList xs (count n xs <= count n (xs ++ ys)) = walkNatList xs True
"p03finB" forall n xs ys . count n xs <= count n (xs ++ ys) = walkNat n (walkList xs True)
"p04fin" forall n xs . count n (n : xs) = walkNat n (S (count n xs))
"p05finE" forall n x xs . walkNat n (walkList xs (prop_05 n x xs)) = walkNat n (walkList xs True)
"p05finF" forall n x xs . walkNat x (walkList xs (prop_05 n x xs)) = walkNat x (walkList xs True)
"p06fin" forall n m . n - (n + m) = walkNat n Z
"p07fin" forall n m . (n + m) - n = walkNat n m
"p08fin" forall k m n . (k + m) - (k + n) = walkNat k (m - n)
"p10fin" forall m . m - m = walkNat m Z
"p15finA" forall x xs . walkNatList xs (len (ins x xs)) = walkNatList xs $ S (len xs)
"p15finB" forall x xs . walkNat x (walkList xs (len (ins x xs))) = walkNat x $ walkList xs $ S (len xs)
"p16finA" forall x xs . walkNat x (prop_16 x xs) = walkNat x True
"p18fin" forall i m . prop_18 i m = walkNat i True
"p20finA" forall xs . walkNatList xs (len (sort xs)) = walkNatList xs (len xs)
"p21fin" forall n m . prop_21 n m = walkNat n True
"p24fin" forall a b . (max a b) === a = walkNat a (b <= a)
"p25fin" forall a b . (max a b) === b = walkNat b (a <= b)
"p26finA" forall x xs ys . walkNatList xs (prop_26 x xs ys) = walkNatList xs True
"p26finB" forall x xs ys . walkList xs (prop_26 x xs ys) = walkNat x $ walkList xs True
"p27finA" forall x xs ys . walkNat x (walkList xs (walkList ys (prop_27 x xs ys))) = walkNat x $ walkList xs $ walkList ys True
"p28finA" forall x xs . walkList xs (prop_28 x xs) = walkNat x $ walkList xs True
"p29finA" forall x xs . walkList xs (prop_29 x xs) = walkNat x $ walkList xs True
"p30finA" forall x xs . walkList xs (prop_30 x xs) = walkNat x $ walkList xs True
"p37finB" forall x xs . walkNatList xs (prop_37 x xs) = walkNatList xs True
"p37finC" forall x xs . walkNat x (prop_37 x xs) = walkNat x $ walkList xs True
"p38finB" forall n xs . walkList xs (count n (xs ++ [n])) = walkNat n $ walkList xs $ S (count n xs)
"p48finB" forall xs . walkNatList xs (prop_48 xs) = walkNatList xs True
"p52finA" forall n xs . walkNatList xs (count n xs) = walkNatList xs (count n (rev xs))
"p53finA" forall n xs . walkNatList xs (count n xs) = walkNatList xs (count n (sort xs))
"p54fin" forall n m . (m + n) - n = walkNat n m
"p57finA" forall n m xs . walkNat n (drop n (take m xs)) = walkNat n (take (m - n) (drop n xs))
"p57finB" forall n m xs . walkNat m (drop n (take m xs)) = walkNat m (take (m - n) (drop n xs))
"p59finA" forall xs ys . walkNatList xs (prop_59 xs ys) = walkNatList xs True
"p60finB" forall xs ys . walkList xs (walkNatList ys (prop_60 xs ys)) = walkList xs $ walkNatList ys True
"p61fin" forall xs ys . last (xs ++ ys) = walkList xs (lastOfTwo xs ys)
"p62finA" forall xs x . walkNatList xs (prop_62 xs x) = walkNatList xs True
"p63finA" forall n xs . walkNatList xs (prop_63 n xs) = walkNatList xs True
"p64fin" forall x xs . last (xs ++ [x]) = walkList xs x
"p65finA" forall i m . prop_65 i m = walkNat i True
"p66fin" forall p xs . prop_66 p xs = walkList xs True
"p68finA" forall n xs . walkNat n (prop_68 n xs) = walkNat n $ walkList xs True
"p68finB" forall n xs . walkNatList xs (prop_68 n xs) = walkNatList xs True
"p69finA" forall n m . prop_69 n m = walkNat n True
"p70finC" forall m n . walkNat m (prop_70 m n) = walkNat m True
"p70finD" forall m n . walkNat n (prop_70 m n) = walkNat n True
"p71finA" forall x y xs . walkNatList xs (prop_71 x y xs) = walkNat x $ walkNatList xs True
"p71finB" forall x y xs . walkNatList xs (prop_71 x y xs) = walkNat y $ walkNatList xs True
"p75fin" forall n m xs . count n xs + count n [m] = walkList xs $ count n (m : xs)
"p76finB" forall n m xs . walkList xs (prop_76 n m xs) = walkNat n $ walkList xs True
"p76finC" forall n m xs . walkNatList xs (prop_76 n m xs) = walkNat m $ walkNatList xs True
"p77finA" forall x xs . walkNatList xs (prop_77 x xs) = walkNatList xs True
"p78finB" forall xs . walkNatList xs (prop_78 xs) = walkNatList xs True
"p85finB" forall xs ys . prop_85 xs ys = walkList xs True
"p85finC" forall xs ys . prop_85 xs ys = walkList ys True
  #-}

walkNat :: Nat -> a -> a
walkNat Z a = a
walkNat (S x) a = walkNat x a

walkList :: [a] -> b -> b
walkList [] a = a
walkList (_:xs) a = walkList xs a

walkNatList :: [Nat] -> a -> a
walkNatList xs a = case xs of
  [] -> a
  y:ys -> walkNat y $ walkNatList ys a
