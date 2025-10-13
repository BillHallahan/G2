module List4 where

import Prelude hiding (zip)

zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

p1 x xs ys = zip (x:xs) ys == zipConcat x xs ys
