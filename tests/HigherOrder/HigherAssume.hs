module HigherAssume where

import Prelude hiding (filter, takeWhile, dropWhile)
import Data.List as L hiding (filter, partition, takeWhile, dropWhile)
import qualified Data.List as L

import G2.Symbolic

data Seq a = Q !Int [a] [a] !Int deriving (Eq)

si (Q x f r y) =
    length f == x && length r == y && x >= y

makeQ :: Int -> [a] -> [a] -> Int -> Seq a
makeQ i xs ys j
  | j > i     = Q (i + j) (xs ++ L.reverse ys) [] 0
  | otherwise = Q i xs ys j

size (Q i _ _ j) = i + j

propA :: (Int -> Int -> Int) -> Seq Int -> Seq Int -> Bool
propA f seq xs
    | size xs > 3 = True
    | otherwise =
        (si xs) ==>
            (bqFoldr f' 0 xs == bqFoldr' f' 0 xs)
        where
                f' x y = assume (f x y == f y x) (f x y) 

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

(==>) :: Bool -> Bool -> Bool
False ==> _ = True
_ ==> b = b
