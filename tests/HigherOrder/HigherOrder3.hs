module HigherOrder3 where

import Prelude hiding (filter, takeWhile, dropWhile)
import Data.List as L hiding (filter, partition, takeWhile, dropWhile)
import qualified Data.List as L

data Seq a = Q !Int [a] [a] !Int deriving (Eq)

si (Q x f r y) =
    length f == x && length r == y && x >= y

makeQ :: Int -> [a] -> [a] -> Int -> Seq a
makeQ i xs ys j
  | j > i     = Q (i + j) (xs ++ L.reverse ys) [] 0
  | otherwise = Q i xs ys j

size (Q i _ _ j) = i + j

propFalse :: (Int -> Int -> Int) -> Seq Int -> Seq Int -> Int
propFalse f seq xs =
    case prop f seq xs of
        True -> 1
        False -> 2

prop :: (Int -> Int -> Int) -> Seq Int -> Seq Int -> Bool
prop f seq xs
    | size xs > 3 = True
    | otherwise =
        (si xs) ==>
            (bqFoldr f 0 xs == bqFoldr' f 0 xs)

revfoldr :: (t -> t1 -> t1) -> t1 -> [t] -> t1
revfoldr _ e [] = e
revfoldr f e (x:xs) = revfoldr f (f x e) xs

revfoldr' :: (t -> a -> a) -> a -> [t] -> a
revfoldr' _ e [] = e
revfoldr' f e (x:xs) = e `seq` revfoldr' f (f x e) xs


bqFoldr  f e (Q _ xs ys _) = L.foldr  f (revfoldr  f e ys) xs
bqFoldr' f e (Q _ xs ys _) = foldr' f (revfoldr' f e ys) xs

foldr' f e [] = e
foldr' f e (x:xs) = f x $! foldr' f e xs

revfoldl :: (t -> t1 -> t) -> t -> [t1] -> t
revfoldl _ e [] = e
revfoldl f e (x:xs) = f (revfoldl f e xs) x

revfoldl' :: (b -> t -> b) -> b -> [t] -> b
revfoldl' _ e [] = e
revfoldl' f e (x:xs) = (\z -> f z x) $! (revfoldl f e xs)

bqFoldl  f e (Q _ xs ys _) = revfoldl  f (L.foldl  f e xs) ys
bqFoldl' f e (Q _ xs ys _) = revfoldl' f (L.foldl' f e xs) ys

(==>) :: Bool -> Bool -> Bool
False ==> _ = True
_ ==> b = b

prop2 :: (Int -> Int -> Int) -> Seq Int -> Seq Int -> Bool
prop2 f seq xs = case prop2' f seq xs of
                    True -> False
                    False -> True

prop2' :: (Int -> Int -> Int) -> Seq Int -> Seq Int -> Bool
prop2' f seq xs
    | size xs > 3 = True
    | otherwise =
        (si seq && si xs) ==>
            (bqFoldr f 0 xs == bqFoldr' f 0 xs
            &&
            bqFoldl f 0 xs == bqFoldl' f 0 xs)


prop3 :: (Int -> Bool) -> Seq Int -> Int -> Seq Int -> Bool
prop3 p seq x xs =
        si xs ==>
            (partition p xs == (filter p xs, filter (not . p) xs)
            &&
            splitWhile p xs == (takeWhile p xs, dropWhile p xs))

partition :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
partition p xs =
  let (ys,zs) = L.partition p (toList xs)
  in (fromList ys, fromList zs)

filter :: (a -> Bool) -> Seq a -> Seq a
filter p xs =
  fromList (L.filter p (toList xs))

splitWhile :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
splitWhile p xs =
  case lview xs of
    Just (x,xs') | p x -> let (front, back) = splitWhile p xs'
                          in (lcons x front, back)
    _                  -> (empty, xs)

takeWhile :: (a -> Bool) -> Seq a -> Seq a
takeWhile p xs =
  case lview xs of
    Just (x,xs') | p x -> lcons x (takeWhile p xs')
    _                  -> empty

dropWhile :: (a -> Bool) -> Seq a -> Seq a
dropWhile p xs =
  case lview xs of
    Just (x,xs') | p x -> dropWhile p xs'
    _                  -> xs

fromList xs = Q (length xs) xs [] 0

toList (Q _ xs ys j)
  | j == 0 = xs
  | otherwise = xs ++ L.reverse ys

empty = Q 0 [] [] 0
lcons x (Q i xs ys j) = Q (i+1) (x:xs) ys j

lview (Q _ [] _ _) = Nothing
lview (Q i (x:xs) ys j) = Just (x, makeQ (i-1) xs ys j)
