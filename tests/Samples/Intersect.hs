module Intersect where

import Prelude hiding (any, intersect, intersectBy, (\\))

intersect               :: (Eq a) => [a] -> [a] -> [a]
intersect               =  intersectBy (==)

intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy _  [] _     =  []
intersectBy _  _  []    =  []
intersectBy eq xs ys    =  [x | x <- xs, any (eq x) ys]

any                     :: (a -> Bool) -> [a] -> Bool
any _ []        = False
any p (x:xs)    = p x || any p xs

commutative :: (Eq a) => [a] -> [a] -> Bool
commutative xs ys = xs `intersect` ys == ys `intersect` xs