module HigherOrder3 where

import Data.List as L

data Seq a = Q !Int [a] [a] !Int

si (Q x f r y) =
    length f == x && length r == y && x >= y

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
