module EquivFalse where

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
  , (>)
  , (-)
  , Int
  , fst
  , snd
  , otherwise
  )

import G2.Plugin
import G2.Plugin.Unsafe

{-# ANN module ("--smt-tuples --higher-order uninterpreted --smt cvc5,z3 --time 90")
    #-}

type Nat = Int

-- code here adapted from HipSpec.hs

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

------------------------------------------------------------------------------
-- From Isaplanner
------------------------------------------------------------------------------

{-# ANN null (SMTEquivIs "nullSMT") #-}
null :: [Nat] -> Bool
null [] = True
null _  = False

nullSMT :: [Nat] -> Bool
nullSMT xs = (smtLen xs) > 0

{-# ANN (++) (SMTEquivIs "appendSMT") #-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

appendSMT :: [a] -> [a] -> [a]
appendSMT xs ys= ys $++ xs

{-# ANN rev (SMTEquivIs "revSMT") #-}
rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

revSMT :: [a] -> [a]
revSMT = smtFoldLeft (\acc x -> [x] $++ acc) []

-- {-# ANN zip (SMTEquivIsWithConfig "zipSMT" "--smt-timeout 20")
--     #-}
-- zip :: [Nat] -> [Nat] -> [(Nat, Nat)]
-- zip [] _ = []
-- zip _ [] = []
-- zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

-- zipSMT :: [Nat] -> [Nat] -> [(Nat, Nat)]
-- zipSMT = smtZip

{-# ANN delete (SMTEquivIs "deleteSMT")
    #-}
delete :: Nat -> [Nat] -> [Nat]
delete _ [] = []
delete n (x:xs) =
  case n === x of
    True -> delete n xs
    False -> x : (delete n xs)

deleteSMT :: Nat -> [Nat] -> [Nat]
deleteSMT x xs = smtReplace xs [x] []

-- {-# ANN len (SMTEquivIs "lenSMT") #-}
-- len :: [a] -> Nat
-- len [] = 0
-- len (_:xs) = 1 + (len xs)

-- lenSMT :: [a] -> Nat
-- lenSMT = smtLen

-- {-# ANN elem (SMTEquivIs "elemSMT") #-}
-- elem :: Nat -> [Nat] -> Bool
-- elem _ [] = False
-- elem n (x:xs) =
--   case n === x of
--     True -> True
--     False -> elem n xs

-- elemSMT :: Nat -> [Nat] -> Bool
-- elemSMT n xs = smtContains xs [n]

{-# ANN drop (SMTEquivIs "dropSMT") #-}
drop :: Nat -> [a] -> [a]
drop x xs | x <= 0 = xs
drop _ [] = []
drop x (_:xs) = drop (x - 1) xs

dropSMT :: Nat -> [a] -> [a]
dropSMT n xs = smtExtract xs n ((smtLen xs) - n)

{-# ANN take (SMTEquivIs "takeSMT") #-}
take :: Nat -> [a] -> [a]
take x _ | x <= 0 = []
take _ [] = []
take x (y:ys) = y : (take (x - 1) ys)

takeSMT :: Nat -> [a] -> [a]
takeSMT n xs = 
  if n >= 0
    then smtExtract xs 0 n
    else xs

{-# ANN count (SMTEquivIs "countSMT") #-}
count :: Nat -> [Nat] -> Nat
count x [] = 0
count x (y:ys) =
  case x === y of
    True -> 1 + (count x ys)
    _ -> count x ys

countSMT :: Nat -> [Nat] -> Nat
countSMT e xs = (smtLen xs) - (smtLen (smtReplace xs [e] []))

-- {-# ANN map (SMTEquivIs "mapSMT") #-}
-- map :: (Nat -> Nat) -> [Nat] -> [Nat]
-- map f [] = []
-- map f (x:xs) = (f x) : (map f xs)

-- mapSMT :: (Nat -> Nat) -> [Nat] -> [Nat]
-- mapSMT = smtMap

{-# ANN takeWhile (SMTEquivIs "takeWhileSMT")
  #-}
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
    smtExtract xs 0 n

{-# ANN dropWhile (SMTEquivIsWithConfig "dropWhileSMT" "--smt-timeout 20")
  #-}
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
    smtExtract xs n (smtLen xs - n)

{-# ANN filter (SMTEquivIs "filterSMT") #-}
filter :: (Nat -> Bool) -> [Nat] -> [Nat]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

filterSMT :: (Nat -> Bool) -> [Nat] -> [Nat]
filterSMT p xs = smtFoldLeft (\acc e -> if p e then [e] $++ acc else acc) [] xs

-- {-# ANN butlast (SMTEquivIs "butlastSMT") #-}
-- butlast :: [Nat] -> [Nat]
-- butlast [] = []
-- butlast [x] = []
-- butlast (x:xs) = x:(butlast xs)

-- butlastSMT :: [Nat] -> [Nat]
-- butlastSMT xs =
--   if smtLen xs == 0
--     then []
--     else smtExtract xs 0 $ smtLen xs - 1

{-# ANN last (SMTEquivIs "lastSMT") #-}
last :: [Nat] -> Nat
last [] = 0
last [x] = x
last (x:xs) = last xs

lastSMT :: [Nat] -> Nat
lastSMT xs =
  if smtLen xs == 0
    then 0
    else smtNth xs $ smtLen xs

{-# ANN ins1 (SMTEquivIs "ins1SMT") #-}
ins1 :: Nat -> [Nat] -> [Nat]
ins1 n [] = [n]
ins1 n (x:xs) =
  case n === x of
    True -> x : xs
    _ -> x : (ins1 n xs)

ins1SMT :: Nat -> [Nat] -> [Nat]
ins1SMT n xs = xs $++ [n]

------------------------------------------------------------------------------
-- From Prod
------------------------------------------------------------------------------

{-# ANN qrev (SMTEquivIs "qrevSMT") #-}
qrev :: [a] -> [a] -> [a]
qrev []     acc = acc
qrev (x:xs) acc = qrev xs (x:acc)

qrevSMT :: [a] -> [a] -> [a]
qrevSMT xs ys = smtReverse xs $++ xs


{-# ANN revflat (SMTEquivIs "revflatSMT") #-}
revflat :: [[a]] -> [a]
revflat []           = []
revflat (xs:xss)     = revflat xss ++ rev xs

revflatSMT :: [[a]] -> [a]
revflatSMT = smtFoldLeft (\acc xs -> acc $++ smtReverse xs) []

{-# ANN qrevflat (SMTEquivIs "qrevflatSMT") #-}
qrevflat :: [[a]] -> [a] -> [a]
qrevflat []           acc = acc
qrevflat (xs:xss)     acc = qrevflat xss (rev xs ++ acc)

qrevflatSMT :: [[a]] -> [a] -> [a]
qrevflatSMT xs ac = smtFoldLeft (\acc xs -> acc $++ smtReverse xs) [] xs $++ ac

{-# ANN rotate (SMTEquivIs "rotateSMT") #-}
rotate :: Nat -> [a] -> [a]
rotate 0     xs     = xs
rotate _     []     = []
rotate n     (x:xs) = rotate (n - 1) (xs ++ [x])

rotateSMT :: Nat -> [a] -> [a]
rotateSMT n xs = let k = n in smtExtract xs n (smtLen xs - n) $++ smtExtract xs 0 n

{-# ANN elem (SMTEquivIs "elemSMT") #-}
elem :: Nat -> [Nat] -> Bool
elem _ []     = False
elem n (x:xs) = (n == x) || elem n xs

-- Still a correct specification
elemSMT :: Nat -> [Nat] -> Bool
elemSMT n xs = smtContains xs [n]

{-# ANN intersect (SMTEquivIs "intersectSMT") #-}
intersect :: [Nat] -> [Nat] -> [Nat]
(x:xs) `intersect` ys | x `elem` ys = x:(xs `intersect` ys)
                      | otherwise = xs `intersect` ys
[] `intersect` ys = []

intersectSMT :: [Nat] -> [Nat] -> [Nat]
intersectSMT xs ys = smtFoldLeft (\acc x -> if smtContains ys [x] then acc else acc $++ [x]) [] xs

{-# ANN union (SMTEquivIs "unionSMT") #-}
union :: [Nat] -> [Nat] -> [Nat]
union (x:xs) ys | x `elem` ys = union xs ys
                | otherwise = x:(union xs ys)
union [] ys = ys

unionSMT :: [Nat] -> [Nat] -> [Nat]
unionSMT xs ys = smtFoldLeft (\acc x -> if smtContains ys [x] then acc $++ [x] else acc) [] xs $++ ys
