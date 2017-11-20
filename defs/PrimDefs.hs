module PrimDefs where

import Prelude (Eq, Ord, Num, Bool, Char, undefined)

(>=) :: Ord a => a -> a -> Bool
(>=) = undefined

(>) :: Ord a => a -> a -> Bool
(>) = undefined

(==) :: Eq a => a -> a -> Bool
(==) = undefined

(/=) :: Eq a => a -> a -> Bool 
(/=) = undefined

(<) :: Ord a => a -> a -> Bool
(<) = undefined

(<=) :: Ord a => a -> a -> Bool 
(<=) = undefined

(&&) :: Bool -> Bool -> Bool
(&&) = undefined

(||) :: Bool -> Bool -> Bool
(||) = undefined

not :: Bool -> Bool
not = undefined

implies :: Bool -> Bool -> Bool
implies = undefined

iff :: Bool -> Bool -> Bool
iff = undefined


(+) :: (Num a) => a -> a -> a
(+) = undefined

(-) :: (Num a) => a -> a -> a
(-) = undefined

(*) :: (Num a) => a -> a -> a
(*) = undefined

(/) :: (Num a) => a -> a -> a
(/) = undefined

negate :: (Num a) => a -> a
negate = undefined

error :: [Char] -> a
error = undefined