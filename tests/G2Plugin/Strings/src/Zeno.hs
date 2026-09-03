{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

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
  , min
  , max
  , (+)
  , (<=)
  , (<)
  , (>=)
  , (-)
  , Int
  , fst
  , snd
  , otherwise
  )

import G2.Plugin
import G2.Plugin.Unsafe

{-# ANN module ("--smt-tuples --higher-order uninterpreted")
    #-}

-- code here adapted from HipSpec.hs

infix 1 =:=

infixr 0 ===>

-- simplification to remove Prop type

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

givenBool :: Bool -> Bool -> Bool
givenBool = given

(===>) :: Bool -> Bool -> Bool
(===>) = given

proveBool :: Bool -> Bool
proveBool lhs = lhs =:= True

(=:=) :: Eq a => a -> a -> Bool
(=:=) = (==)

-- everything here mainly copied from HipSpec, with some simplifications

type Nat = Int

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

(===) :: Eq a => a -> a -> Bool
x === y = x == y

-- List functions

{-# ANN null (SMTEquivIs "nullSMT") #-}
null :: [Nat] -> Bool
null [] = True
null _  = False

nullSMT :: [Nat] -> Bool
nullSMT xs = (smtLen xs) == 0

{-# ANN (++) (SMTEquivIs "appendSMT") #-}
(++) :: [Nat] -> [Nat] -> [Nat]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

appendSMT :: [Nat] -> [Nat] -> [Nat]
appendSMT = ($++)

{-# ANN rev (SMTEquivIsWithConfig "revSMT" "--smt cvc5")
    #-}
rev :: [Nat] -> [Nat]
rev [] = []
rev (x:xs) = rev xs ++ [x]

revSMT :: [Nat] -> [Nat]
revSMT = smtReverse

{-# ANN zip (SMTEquivIsWithConfig "zipSMT" "--smt-timeout 20")
    #-}
zip :: [Nat] -> [Nat] -> [(Nat, Nat)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

zipSMT :: [Nat] -> [Nat] -> [(Nat, Nat)]
zipSMT = smtZip

{-# ANN delete (SMTEquivIsWithConfig "deleteSMT" "--smt cvc5")
    #-}
delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n === x of
    True -> delete n xs
    False -> x : (delete n xs)

deleteSMT :: Nat -> [Nat] -> [Nat]
deleteSMT x xs = smtReplaceAll xs [x] []

{-# ANN len (SMTEquivIs "lenSMT") #-}
len :: [Nat] -> Nat
len [] = 0
len (_:xs) = 1 + (len xs)

lenSMT :: [Nat] -> Nat
lenSMT = smtLen

{-# ANN elem (SMTEquivIs "elemSMT") #-}
elem :: Nat -> [Nat] -> Bool
elem _ [] = False
elem n (x:xs) =
  case n === x of
    True -> True
    False -> elem n xs

elemSMT :: Nat -> [Nat] -> Bool
elemSMT n xs = smtContains xs [n]

{-# ANN drop (SMTEquivIs "dropSMT") #-}
drop :: Nat -> [Nat] -> [Nat]
drop x xs | x <= 0 = xs
drop _ [] = []
drop x (_:xs) = drop (x - 1) xs

dropSMT :: Nat -> [Nat] -> [Nat]
dropSMT n xs = 
  if n >= 0
    then smtExtract xs n ((smtLen xs) - n)
    else xs

{-# ANN take (SMTEquivIs "takeSMT") #-}
take :: Nat -> [Nat] -> [Nat]
take x _ | x <= 0 = []
take _ [] = []
take x (y:ys) = y : (take (x - 1) ys)

takeSMT :: Nat -> [Nat] -> [Nat]
takeSMT n xs = smtExtract xs 0 n

{-# ANN count (SMTEquivIsWithConfig "countSMT" "--smt cvc5")
    #-}
count :: Nat -> [Nat] -> Nat
count x [] = 0
count x (y:ys) =
  case x === y of
    True -> 1 + (count x ys)
    _ -> count x ys

countSMT :: Nat -> [Nat] -> Nat
countSMT e xs = (smtLen xs) - (smtLen (smtReplaceAll xs [e] []))

{-# ANN map (SMTEquivIs "mapSMT") #-}
map :: (Nat -> Nat) -> [Nat] -> [Nat]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

mapSMT :: (Nat -> Nat) -> [Nat] -> [Nat]
mapSMT = smtMap

{-# ANN takeWhile (SMTEquivIs "takeWhileSMT") #-}
takeWhile :: (Nat -> Bool) -> [Nat] -> [Nat]
takeWhile _ [] = []
takeWhile p (x:xs) =
  case p x of
    True -> x : (takeWhile p xs)
    _ -> []

takeWhileSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
takeWhileSMT p xs =
    let
        bs = smtMap p xs
        n = smtIndexOf bs [False] 0
    in
    case n of
        -1 -> xs
        _ -> smtExtract xs 0 n
    

-- takeWhileSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
-- takeWhileSMT p xs =
--   let (as', _) = exists2 (\as bs -> xs `smtEq` (as $++ bs) &&
--                                     smtFoldLeft (\acc e -> acc && p e) True as && 
--                                     smtFoldLeft (\acc e -> acc && not (p e)) True (smtAt bs 0))
--   in as'

{-# ANN dropWhile (SMTEquivIsWithConfig "dropWhileSMT" "") #-}
dropWhile :: (Nat -> Bool) -> [Nat] -> [Nat]
dropWhile _ [] = []
dropWhile p (x:xs) =
  case p x of
    True -> dropWhile p xs
    _ -> x:xs

dropWhileSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
dropWhileSMT p xs =
    let
        bs = smtMap p xs
        n = smtIndexOf bs [False] 0
    in
    case n of
        -1 -> []
        _ -> smtExtract xs n (smtLen xs - n)

-- dropWhileSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
-- dropWhileSMT p xs =
--   let (_, bs') = exists2 (\as bs -> xs `smtEq` (as $++ bs) &&
--                                     smtFoldLeft (\acc e -> acc && p e) True as && 
--                                     smtFoldLeft (\acc e -> acc && not (p e)) True (smtAt bs 0))
--   in bs'

{-# ANN filter (SMTEquivIs "filterSMT") #-}
filter :: (Nat -> Bool) -> [Nat] -> [Nat]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

filterSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
filterSMT p xs = smtFoldLeft (\acc e -> if p e then acc $++ [e] else acc) [] xs

{-# ANN butlast (SMTEquivIs "butlastSMT") #-}
butlast :: [Nat] -> [Nat]
butlast [] = []
butlast [x] = []
butlast (x:xs) = x:(butlast xs)

butlastSMT :: [Nat] -> [Nat]
butlastSMT xs =
  if smtLen xs == 0
    then []
    else smtExtract xs 0 $ smtLen xs - 1

{-# ANN last (SMTEquivIs "lastSMT") #-}
last :: [Nat] -> Nat
last [] = 0
last [x] = x
last (x:xs) = last xs

lastSMT :: [Nat] -> Nat
lastSMT xs =
  if smtLen xs == 0
    then 0
    else smtNth xs $ smtLen xs - 1

-- {-# ANN sorted (SMTEquivIs "sortedSMT") #-}
sorted :: [Nat] -> Bool
sorted [] = True
sorted [x] = True
sorted (x:y:ys) = (x <= y) && sorted (y:ys)

-- sortedSMT :: [Nat] -> Bool
-- sortedSMT xs =
--   case xs of
--     (y:ys) -> let (r, _) = smtFoldLeft (\(valid, e') e -> (valid && (e' <= e), e)) (True, y) ys
--               in r
--     _ -> True

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

{-# ANN ins1 (SMTEquivIs "ins1SMT") #-}
ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n === x of
    True -> x : xs
    _ -> x : (ins1 n xs)

ins1SMT :: Nat -> [Nat] -> [Nat]
ins1SMT n xs =
  if smtContains xs [n]
    then xs
    else xs $++ [n]

sort :: [Nat] -> [Nat]
sort [] = []
sort (x:xs) = insort x (sort xs)

butlastConcat :: [Nat] -> [Nat] -> [Nat]
butlastConcat xs [] = butlast xs
butlastConcat xs ys = xs ++ butlast ys

lastOfTwo :: [Nat] -> [Nat] -> Nat
lastOfTwo xs [] = last xs
lastOfTwo _ ys = last ys

zipConcat :: Nat -> [Nat] -> [Nat] -> [(Nat, Nat)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

height :: Tree Nat -> Nat
height Leaf = 0
height (Node l x r) = 1 + (max (height l) (height r))

mirror :: Tree Nat -> Tree Nat
mirror Leaf = Leaf
mirror (Node l x r) = Node (mirror r) x (mirror l)

prop_01 :: Nat -> [Nat] -> Bool
prop_01 n xs
  = (take n xs ++ drop n xs =:= xs)

prop_02 :: Nat -> [Nat] -> [Nat] -> Bool
prop_02 n xs ys
  = (count n xs + count n ys =:= count n (xs ++ ys))

prop_03 :: Nat -> [Nat] -> [Nat] -> Bool
prop_03 n xs ys
  = proveBool (count n xs <= count n (xs ++ ys))

prop_04 :: Nat -> [Nat] -> Bool
prop_04 n xs
  = (1 + (count n xs) =:= count n (n : xs))

prop_05 :: Nat -> Nat -> [Nat] -> Bool
prop_05 n x xs
  = n =:= x ===> 1 + (count n xs) =:= count n (x : xs)

prop_06 :: Nat -> Nat -> Bool
prop_06 n m
  = (n - (n + m) =:= 0)

prop_07 :: Nat -> Nat -> Bool
prop_07 n m
  = ((n + m) - n =:= m)

prop_08 :: Nat -> Nat -> Nat -> Bool
prop_08 k m n
  = ((k + m) - (k + n) =:= m - n)

prop_09 :: Nat -> Nat -> Nat -> Bool
prop_09 i j k
  = ((i - j) - k =:= i - (j + k))

prop_10 :: Nat -> Bool
prop_10 m
  = (m - m =:= 0)

prop_11 :: [Nat] -> Bool
prop_11 xs
  = (drop 0 xs =:= xs)

prop_12 :: Nat -> (Nat -> Nat) -> [Nat] -> Bool
prop_12 n f xs
  = (drop n (map f xs) =:= map f (drop n xs))

prop_13 :: Nat -> Nat -> [Nat] -> Bool
prop_13 n x xs
  = (drop (1 + n) (x : xs) =:= drop n xs)

prop_14 :: (Nat -> Bool) -> [Nat] -> [Nat] -> Bool
prop_14 p xs ys
  = (filter p (xs ++ ys) =:= (filter p xs) ++ (filter p ys))

prop_15 :: Nat -> [Nat] -> Bool
prop_15 x xs
  = (len (ins x xs) =:= (1 + (len xs)))

prop_16 :: Nat -> [Nat] -> Bool
prop_16 x xs
  = xs =:= [] ===> last (x:xs) =:= x

prop_17 :: Nat -> Bool
prop_17 n
  = (n <= 0 =:= n === 0)

prop_18 :: Nat -> Nat -> Bool
prop_18 i m
  = proveBool (i < 1 + (i + m))

prop_19 :: Nat -> [Nat] -> Bool
prop_19 n xs
  = (len (drop n xs) =:= len xs - n)

prop_20 :: [Nat] -> Bool
prop_20 xs
  = (len (sort xs) =:= len xs)

prop_21 :: Nat -> Nat -> Bool
prop_21 n m
  = proveBool (n <= (n + m))

prop_22 :: Nat -> Nat -> Nat -> Bool
prop_22 a b c
  = (max (max a b) c =:= max a (max b c))

prop_23 :: Nat -> Nat -> Bool
prop_23 a b
  = (max a b =:= max b a)

prop_24 :: Nat -> Nat -> Bool
prop_24 a b
  = ((max a b) === a =:= b <= a)

prop_25 :: Nat -> Nat -> Bool
prop_25 a b
  = ((max a b) === b =:= a <= b)

prop_26 :: Nat -> [Nat] -> [Nat] -> Bool
prop_26 x xs ys
  = givenBool (x `elem` xs)
  ( proveBool (x `elem` (xs ++ ys)) )

prop_27 :: Nat -> [Nat] -> [Nat] -> Bool
prop_27 x xs ys
  = givenBool (x `elem` ys)
  ( proveBool (x `elem` (xs ++ ys)) )

prop_28 :: Nat -> [Nat] -> Bool
prop_28 x xs
  = proveBool (x `elem` (xs ++ [x]))

prop_29 :: Nat -> [Nat] -> Bool
prop_29 x xs
  = proveBool (x `elem` ins1 x xs)

prop_30 :: Nat -> [Nat] -> Bool
prop_30 x xs
  = proveBool (x `elem` ins x xs)

prop_31 :: Nat -> Nat -> Nat -> Bool
prop_31 a b c
  = (min (min a b) c =:= min a (min b c))

prop_32 :: Nat -> Nat -> Bool
prop_32 a b
  = (min a b =:= min b a)

prop_33 :: Nat -> Nat -> Bool
prop_33 a b
  = (min a b === a =:= a <= b)

prop_34 :: Nat -> Nat -> Bool
prop_34 a b
  = (min a b === b =:= b <= a)

prop_35 :: [Nat] -> Bool
prop_35 xs
  = (dropWhile (\_ -> False) xs =:= xs)

prop_36 :: [Nat] -> Bool
prop_36 xs
  = (takeWhile (\_ -> True) xs =:= xs)

prop_37 :: Nat -> [Nat] -> Bool
prop_37 x xs
  = proveBool (not (x `elem` delete x xs))

prop_38 :: Nat -> [Nat] -> Bool
prop_38 n xs
  = (count n (xs ++ [n]) =:= 1 + (count n xs))

prop_39 :: Nat -> Nat -> [Nat] -> Bool
prop_39 n x xs
  = (count n [x] + count n xs =:= count n (x:xs))

prop_40 :: [Nat] -> Bool
prop_40 xs
  = (take 0 xs =:= [])

prop_41 :: Nat -> (Nat -> Nat) -> [Nat] -> Bool
prop_41 n f xs
  = (take n (map f xs) =:= map f (take n xs))

prop_42 :: Nat -> Nat -> [Nat] -> Bool
prop_42 n x xs
  = (take n (x:xs) =:= x : (take (n - 1) xs))

prop_43 :: (Nat -> Bool) -> [Nat] -> Bool
prop_43 p xs
  = (takeWhile p xs ++ dropWhile p xs =:= xs)

-- prop_44 :: Nat -> [Nat] -> [Nat] -> Bool
-- prop_44 x xs ys
--   = (zip (x:xs) ys =:= zipConcat x xs ys)

-- prop_45 :: Nat -> Nat -> [Nat] -> [Nat] -> Bool
-- prop_45 x y xs ys
--   = (zip (x:xs) (y:ys) =:= (x, y) : zip xs ys)

-- prop_46 :: [Nat] -> Bool
-- prop_46 xs
--   = (zip ([] :: [Nat]) xs =:= [])

prop_47 :: Tree Nat -> Bool
prop_47 a
  = (height (mirror a) =:= height a)

prop_48 :: [Nat] -> Bool
prop_48 xs
  = givenBool (not (null xs))
  ( (butlast xs ++ [last xs] =:= xs) )

prop_49 :: [Nat] -> [Nat] -> Bool
prop_49 xs ys
  = (butlast (xs ++ ys) =:= butlastConcat xs ys)

prop_50 :: [Nat] -> Bool
prop_50 xs
  = (butlast xs =:= take (len xs - 1) xs)

prop_51 :: [Nat] -> Nat -> Bool
prop_51 xs x
  = (butlast (xs ++ [x]) =:= xs)

prop_52 :: Nat -> [Nat] -> Bool
prop_52 n xs
  = (count n xs =:= count n (rev xs))

prop_53 :: Nat -> [Nat] -> Bool
prop_53 n xs
  = (count n xs =:= count n (sort xs))

prop_54 :: Nat -> Nat -> Bool
prop_54 n m
  = ((m + n) - n =:= m)

prop_55 :: Nat -> [Nat] -> [Nat] -> Bool
prop_55 n xs ys
  = (drop n (xs ++ ys) =:= drop n xs ++ drop (n - len xs) ys)

prop_56 :: Nat -> Nat -> [Nat] -> Bool
prop_56 n m xs
  = (drop n (drop m xs) =:= drop (n + m) xs)

prop_57 :: Nat -> Nat -> [Nat] -> Bool
prop_57 n m xs
  = (drop n (take m xs) =:= take (m - n) (drop n xs))

-- prop_58 :: Nat -> [Nat] -> [Nat] -> Bool
-- prop_58 n xs ys
--   = (drop n (zip xs ys) =:= zip (drop n xs) (drop n ys))

prop_59 :: [Nat] -> [Nat] -> Bool
prop_59 xs ys
  = ys =:= [] ===> last (xs ++ ys) =:= last xs

prop_60 :: [Nat] -> [Nat] -> Bool
prop_60 xs ys
  = givenBool (not (null ys))
  ( (last (xs ++ ys) =:= last ys) )

prop_61 :: [Nat] -> [Nat] -> Bool
prop_61 xs ys
  = (last (xs ++ ys) =:= lastOfTwo xs ys)

prop_62 :: [Nat] -> Nat -> Bool
prop_62 xs x
  = givenBool (not (null xs))
  ( (last (x:xs) =:= last xs) )

prop_63 :: Nat -> [Nat] -> Bool
prop_63 n xs
  = givenBool (n < len xs)
  ( (last (drop n xs) =:= last xs) )

prop_64 :: Nat -> [Nat] -> Bool
prop_64 x xs
  = (last (xs ++ [x]) =:= x)

prop_65 :: Nat -> Nat -> Bool
prop_65 i m =
  proveBool (i < 1 + (m + i))

prop_66 :: (Nat -> Bool) -> [Nat] -> Bool
prop_66 p xs
  = proveBool (len (filter p xs) <= len xs)

prop_67 :: [Nat] -> Bool
prop_67 xs
  = (len (butlast xs) =:= len xs - 1)

prop_68 :: Nat -> [Nat] -> Bool
prop_68 n xs
  = proveBool (len (delete n xs) <= len xs)

prop_69 :: Nat -> Nat -> Bool
prop_69 n m
  = proveBool (n <= (m + n))

prop_70 :: Nat -> Nat -> Bool
prop_70 m n
  = givenBool (m <= n)
  ( proveBool (m <= 1 + n) )

prop_71 :: Nat -> Nat -> [Nat] -> Bool
prop_71 x y xs
  = given (x === y =:= False)
  ( (elem x (ins y xs) =:= elem x xs) )

prop_72 :: Nat -> [Nat] -> Bool
prop_72 i xs
  = (rev (drop i xs) =:= take (len xs - i) (rev xs))

prop_73 :: (Nat -> Bool) -> [Nat] -> Bool
prop_73 p xs
  = (rev (filter p xs) =:= filter p (rev xs))

prop_74 :: Nat -> [Nat] -> Bool
prop_74 i xs
  = (rev (take i xs) =:= drop (len xs - i) (rev xs))

prop_75 :: Nat -> Nat -> [Nat] -> Bool
prop_75 n m xs
  = (count n xs + count n [m] =:= count n (m : xs))

prop_76 :: Nat -> Nat -> [Nat] -> Bool
prop_76 n m xs
  = given (n === m =:= False)
  ( (count n (xs ++ [m]) =:= count n xs) )

prop_77 :: Nat -> [Nat] -> Bool
prop_77 x xs
  = givenBool (sorted xs)
  ( proveBool (sorted (insort x xs)) )

prop_78 :: [Nat] -> Bool
prop_78 xs
  = proveBool (sorted (sort xs))

prop_79 :: Nat -> Nat -> Nat -> Bool
prop_79 m n k
  = ((1 + m - n) - (1 + k) =:= (m - n) - k)

prop_80 :: Nat -> [Nat] -> [Nat] -> Bool
prop_80 n xs ys
  = (take n (xs ++ ys) =:= take n xs ++ take (n - len xs) ys)

prop_81 :: Nat -> Nat -> [Nat] -> Bool
prop_81 n m xs {- ys -}
  = (take n (drop m xs) =:= drop m (take (n + m) xs))

-- prop_82 :: Nat -> [Nat] -> [Nat] -> Bool
-- prop_82 n xs ys
--   = (take n (zip xs ys) =:= zip (take n xs) (take n ys))

-- prop_83 :: [Nat] -> [Nat] -> [Nat] -> Bool
-- prop_83 xs ys zs
--   = (zip (xs ++ ys) zs =:=
--            zip xs (take (len xs) zs) ++ zip ys (drop (len xs) zs))

-- prop_84 :: [Nat] -> [Nat] -> [Nat] -> Bool
-- prop_84 xs ys zs
--   = (zip xs (ys ++ zs) =:=
--            zip (take (len ys) xs) ys ++ zip (drop (len ys) xs) zs)

-- prop_85 :: [Nat] -> [Nat] -> Bool
-- prop_85 xs ys
--   = (len xs =:= len ys) ===>
--     (zip (rev xs) (rev ys) =:= rev (zip xs ys))
