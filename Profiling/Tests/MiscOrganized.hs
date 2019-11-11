module BenchmarkTests where

import qualified Data.List as L
import qualified Data.Set as S
import Data.Char (digitToInt)
import Data.Array as A

----------------------------------------
-- Tests (Work for both) --
--------------------------------------
reverse' :: (Eq a) => [a] -> [a]
reverse' list = reverse'' list []
    where
       reverse'' [] reversed     = reversed
       reverse'' (x:xs) reversed = reverse'' xs (x:reversed)

-- infinite recursion after state 6
prop_reverse_wrong :: (Eq a) => [a] -> [a] -> Bool
prop_reverse_wrong a b = a /= (reverse' b)

compress :: (Eq a) => [a] -> [a]
compress (x:ys@(y:_))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

-- SM version uses far lesser states (6,000 to 29,000), but takes about same time for n = 500
-- (28,000 states to 290,000) states for n = 800, but about same time still
reverseCompress :: [Int] -> [Int] -> [Int]
reverseCompress a b =
    case reverse' a of
        (x:xs) -> compress b
        [] -> []

-- infinite recursion after state 6
prop_compress_wrong :: (Eq a) => [a] -> [a] -> Bool
prop_compress_wrong a b = (head a) /= (head b)

runLengthEncode :: (Eq a) => [a] -> [(Int, a)]
runLengthEncode [] = []
runLengthEncode (x:xs) = (length $ x : takeWhile (==x) xs, x) : runLengthEncode (dropWhile (==x) xs)

-- infinite recursion after state 6
runLengthEncodeAnyEffect :: (Eq a) => [a] -> [(Int, a)] -> Bool
runLengthEncodeAnyEffect a b = (length a) == (length b)

-- unequal redir objs or symb objs present in both (fixed)
insertAt' :: a -> [a] -> Int -> [a]
insertAt' x ys 0 = x:ys
insertAt x (y:ys) n = y:insertAt' x ys (n-1)

-- Stack
-- Test 1: checkN - both similar
-- Test 2: checkNTest assume nNotZero - both similar (n = 5000)
type Stack = [Int]

push :: Stack -> Int -> Stack
push s x = x:s

top :: Stack -> Int
top (x:xs) = x
top [] = error "Stack empty"

pushN :: Stack -> Int -> Int -> Stack
pushN s x n = (replicate n x) ++ s

checkN :: Stack -> Int -> Int -> Bool
checkN (x:xs) v n
    | n > 0 = if (x == v) then checkN xs v (n - 1) else False
    | otherwise = True

nNotZero :: Stack -> Int -> Bool -> Bool
nNotZero _ n _  = n > 0

checkNTest :: Int -> Int -> Bool
checkNTest v n = checkN (pushN [1] v (n + 10)) v (n + 12)

-- assertion for pushN
checkNAss :: Stack -> Int -> Int -> Stack -> Bool
checkNAss _ x count res = checkN res x count

checkNSub1Pos :: (Eq a) => a -> [a] -> Int -> [a] -> Bool
checkNSub1Pos x _ pos res = (res !! (pos - 1)) == x

-- (n = 10000)
listEmptyToNum :: Int -> Int -> [Int]
listEmptyToNum a b =
    let y = replicate (b + 10) a
        z = case y of
                [] -> 1:[]
                (x:xs) -> a:(x:xs)
    in case (head z) of
        1 -> y
        _ -> [2]

listEmptyToNumAss :: Int -> Int -> [Int] -> Bool
listEmptyToNumAss _ _ res = (length res) < 3

safeLast :: [Int] -> Int
safeLast x = last x'
    where
    x' = case x of
        [] -> 1:[]
        (y:ys) -> x

-- n = 3000
range' :: Int -> Int -> [Int]
range' lo hi
    | lo <= hi = lo : range' (lo + 1) hi
    | otherwise = []

rangeAssume :: Int -> Int -> [Int] -> Bool
rangeAssume lo hi _ = (lo == 10) && (hi >= 15)

rangeAssert :: Int -> Int -> [Int] -> Bool
rangeAssert lo hi res = (length res) == (hi-lo)

rangeAssert2 :: Int -> Int -> [Int] -> Bool
rangeAssert2 lo hi res = (head res) == (lo+1)

-- Pascal's triangle
rows :: Int -> [[Integer]]
rows n = take n $ iterate next [1]

next :: [Integer] -> [Integer]
next xs = zipWith (+) (xs ++ [0]) (0 : xs)

-- insertion sort
-- runs very slowly for n > 250
-- goto.ucsd.edu/~nvazou/cufp15_liquidHaskell/04-case-study-insertsort.html#/goal-verified-insertion-sort
-- Originally: unequal symbobjs, then bad type in retLam error
insertionSort :: (Ord a) => [a] -> [a]
insertionSort [] = []
insertionSort (x:xs) = insert'' x (insertionSort xs)

insert'' :: (Ord a) => a -> [a] -> [a]
insert'' x [] = x : []
insert'' x (y:ys)
  | x <= y = x : y : ys
  | otherwise = y : insert'' x ys

-- works for both, but no merging takes place
zipInt :: [Int] -> [Int] -> [(Int, Int)]
zipInt [] [] = []
zipInt (x:xs) (y:ys) = (x, y): zip' xs ys
zipInt _ _ = error "Unequal length of lists"

zipAssertInt :: [Int] -> [Int] -> [(Int,Int)] -> Bool
zipAssertInt a _ res = (head a) == (fst (head res))

append' :: [Int] -> [Int] -> [Int]
append' c d = case c of
    [] -> d
    (z:zs) -> z:(append' zs d)

appendAss :: [Int] -> [Int] -> [Int] -> Bool
appendAss a b res = (head a) == (head res)

appendOneStart :: [Int] -> Int -> [Int]
appendOneStart y z =
    case z of
        1 -> 1:x
        _ -> 2:x
    where 
    x = case y of
        [] -> 1:[]
        _ -> y

appendOneEnd :: [Int] -> Int -> [Int]
appendOneEnd y z =
    case z of
        1 -> x ++ [1]
        _ -> x
    where 
    x = case y of
        [] -> 1:[]
        _ -> y

appendOneEndAss :: [Int] -> Int -> [Int] -> Bool
appendOneEndAss _ _ res = (last res) == 1

appendOneStartAss :: [Int] -> Int -> [Int] -> Bool
appendOneStartAss _ _ res = (head res) == 2

get :: [a] -> Int -> a
get xs j = case xs of
            h:t -> case j == 0 of
                True -> h
                False -> get t (j - 1)

repl :: Int -> [Int]
repl x = x:repl (x+1)

repl_get :: Int -> Int -> Int -> Int
repl_get i j k = (get (repl i) k) + (get (repl j) k)

-- originially did't work with merge-states (no results) due to NonDets piling on faster than they are reduced within the limit for number of states
-- works with limit on depth of tree
repl_prop :: Int -> Int -> Int -> Bool
repl_prop i k res = i == res


--------------------------------------------------
-- Too slow for both --
--------------------------------------------------

-- unable to find violation in 5000 states
break' :: (Int -> Bool) -> [Int] -> ([Int], [Int])
break' _ xs@[] =  (xs, xs)
break' p xs@(x:xs')
    | p x        =  ([], xs)
    | otherwise  =  let (ys, zs) = break' p xs' 
                    in (x:ys,zs)

breakAssert :: (Int -> Bool) -> [Int] -> ([Int], [Int]) -> Bool
breakAssert _ _ (a, b) = (length a) == (length b)

-- works, but only 1 result, too slow for anything else
validateLuhnStr :: String -> Bool
validateLuhnStr n = validLength && val `mod` 10 == 0
   where 
    digits = concat $ fmap (fmap digitToInt) (words n)    
    validLength = length digits > 1
    val = sum $ zipWith doubleEven [0..] (reverse digits)
    doubleEven :: Int -> Int -> Int
    doubleEven n x | n `mod` 2 == 1 = let dbl = 2*x in if (dbl > 9) then dbl - 9 else dbl
                   | otherwise = x

-- Binary Tree
-- Test 1: treeHeightAssSimple: too slow for both
-- Test 2: treeInsertCheck: unequalsymObjs or redirObjs -- partly fixed now
-- Test 3: treeHeightAss: works about the same, no result at n = 1000, but works when you remove check for number of params in eval case
data Tree a = Nil | Node (Tree a) a (Tree a) deriving Eq 

insert :: (Ord a) => Tree a -> a -> Tree a
insert Nil x = Node Nil x Nil
insert (Node t1 y t2) x 
    | y == x = Node t1 y t2
    | y < x = Node t1 y (insert t2 x)
    | y > x = Node (insert t1 x) y t2

insertWrong :: (Ord a) => Tree a -> a -> Tree a
insertWrong Nil x = Node Nil x Nil
insertWrong (Node t1 y t2) x 
    | y <= x = Node t1 y (insertWrong t2 x)
    | y > x = Node (insertWrong t1 x) y t2
     
height :: Tree a -> Int
height Nil = 0
height (Node t1 x t2) = 1 + (max (height t1) (height t2))

contains :: (Ord a) => Tree a -> a -> Bool
contains Nil x = False
contains (Node t1 y t2) x
    | y == x = True
    | y < x = contains t2 x
    | y > x = contains t1 x

treeHeightAssSimple :: Tree Int -> Int -> Bool
treeHeightAssSimple _ a = a < 3

treeHeightTwo :: Tree Int -> Int -> Bool
treeHeightTwo a _ = (a == Node (Node Nil 0 Nil) 0 (Node Nil 0 Nil))

-- with varIdsInPC for AssumePC as just the 'x' : runs without error but shows wrong results
-- with varIdsInPC for AssumePC as all vars in the PC : runs without error for 500, but unsatisfiable value in NonDetExpr for 1000
treeInsertCheck :: (Ord a) => Tree a -> a -> Bool
treeInsertCheck t x = contains (insert t x) x
    where t' = insert t x

matchingParens :: String -> Bool
matchingParens xs = null $ foldl f [] bs
    where bs = filter (`elem` "[]{}()") xs
          f a b
            | b `elem` "[({" = b:a
            | null a = "nope"
            | otherwise = if c b == head a then tail a else "nope"
          c ']' = '['
          c ')' = '('
          c '}' = '{'
          c _   = '%'

matchingParensAssume :: String -> Bool -> Bool
matchingParensAssume str _ = (length str) == 5

treeFoo :: Int -> Tree Int -> Int
treeFoo in1 in2 =
    case treeBaz in2 in1 of
        Node _ val _ -> val
        _ -> 4

treeBaz :: Tree Int -> Int -> Tree Int
treeBaz y x =
    case x of
        1 -> case y of
                Node a _ c -> Node (treeBaz a x) 1 (treeBaz c x)
                _ -> Node Nil 0 Nil
        _ -> case y of
                Node a _ c -> Node (treeBaz a x) 2 (treeBaz c x) 
                _ -> Node Nil 3 Nil


------------------------------------------------
-- Error: Unequal symbobjs or redir objs --
-- Now: 
-- G2: unmatched expr[Type (TyCon (Name "Int" (Just "GHC.Types") 8214565720323789223 Nothing) TYPE)]
-- CallStack (from HasCallStack):
--   error, called at src/G2/Execution/Rules.hs:332:18 in g2-0.1.0.0-6gZe5TCxUAf1VS3DO2Gzcc:G2.Execution.Rules
--   CallStack (from -prof):
--   both work with maxDepth set to 3
-----------------------------------------------
qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort lhs ++ [x] ++ qsort rhs
    where 
        lhs = filter  (< x) xs
        rhs = filter (>= x) xs

data Expr = Num Int           -- atom
        | Str String          -- atom
        | Op BinOp Expr Expr  -- compound
        deriving (Show)

data BinOp = Add | Concat deriving (Show)

interp :: Expr -> Expr
interp x@(Num _) = x
interp x@(Str _) = x
interp (Op Add a b) = Num (i a + i b)
  where i x = case interp x of Num a -> a
interp (Op Concat (Str a) (Str b)) = Str (a ++ b)

-------------------------------------------------
-- EvalCase returns nothing --
------------------------------------------------
breakUnder5 :: [Int] -> ([Int], [Int])
breakUnder5 xs@[] =  (xs, xs)
breakUnder5 xs@(x:xs')
    | x < 5        =  ([], xs)
    | otherwise  =  let (ys, zs) = breakUnder5 xs' 
                    in (x:ys,zs)

breakUnder5Assert :: [Int] -> ([Int], [Int]) -> Bool
breakUnder5Assert  _ (a, b) = (length a) == (length b)

-------------------------------------------------
-- EvalVar: BadInput error (in both) -- 
-- ---------------------------------------------

-- check if 2 lists are sublists of another
sublist :: (Ord a) => [a] -> [a] -> Maybe Ordering
sublist xs ys | xs == ys = Just EQ
              | xs `L.isInfixOf` ys = Just LT
              | ys `L.isInfixOf` xs = Just GT
              | otherwise = Nothing

data Sublist = Equal | Sublist | Superlist | Unequal deriving (Eq, Show, Ord)

sublistWithSet :: Ord a => [a] -> [a] -> Sublist
sublistWithSet xs ys
  -- | S.disjoint f l = Unequal
  | S.isProperSubsetOf f l = Sublist
  | S.isSubsetOf f l = Equal
  | S.isSubsetOf l f = Superlist
  | otherwise = Unequal
  where
    f = S.fromList xs
    l = S.fromList ys

binarySearch' :: Ord a => A.Array Int a -> (Int, Int) -> a -> Maybe Int
binarySearch' array (left, right) x
  | right < left = Nothing
  | x < val = binarySearch' array (left, mid - 1) x
  | x > val = binarySearch' array (mid + 1, right) x
  | otherwise = Just mid
  where
    mid = (left + right) `div` 2
    val = array A.! mid

binarySearch :: Ord a => Array Int a -> a -> Maybe Int
binarySearch array = binarySearch' array (A.bounds array)

------------------------------------------------------
-- Hangs in both --
-----------------------------------------------------
type Vector a = [a]

vectorAdd :: (Eq a, Num a) => Vector a -> Vector a -> Vector a
vectorAdd (x:xs) (y:ys) = (x+y):(vectorAdd xs ys) 
vectorAdd (x:xs) [] = (x:xs)
vectorAdd [] (y:ys) = (y:ys)
vectorAdd [] [] = []

vectorAddAssert :: (Eq a, Num a) => Vector a -> Vector a -> Vector a -> Bool
vectorAddAssert a b res = (head res) == (head a)

zip' :: [a] -> [b] -> [(a, b)]
zip' [] [] = []
zip' (x:xs) (y:ys) = (x, y): zip' xs ys
zip' _ _ = error "Unequal length of lists"

-- hangs for some reason in both -- bug in src/G2/Execution/Rules traceType: 
zipAssert :: (Eq a) => [a] -> [b] -> [(a,b)] -> Bool
zipAssert a _ res = (head a) == (fst (head res))

validateLuhn :: [Int] -> Bool
validateLuhn idn = validLength && val `mod` 10 == 0
   where 
    validLength = length idn  > 1
    val = sum $ zipWith doubleEven [0..] (reverse idn)
    doubleEven :: Int -> Int -> Int
    doubleEven n x | n `mod` 2 == 1 = let dbl = 2*x in if (dbl > 9) then dbl - 9 else dbl
                   | otherwise = x

validateLuhnAssume :: [Int] -> Bool -> Bool
validateLuhnAssume n _ = (length n) == 3 

validateLuhnAssert :: [Int] -> Bool -> Bool
validateLuhnAssert _ res = (res == False)

