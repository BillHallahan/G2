module List3 where

import Prelude hiding ((++), filter)

(++) :: [Int] -> [Int] -> [Int]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

filterBad :: (Int -> Bool) -> [Int] -> [Int]
filterBad _ [] = []
filterBad p [x] = [x]
filterBad p (x:xs) =
  case p x of
    True -> x : (filterBad p xs)
    _ -> filterBad p xs

p1False p x ys
  = (filterBad p ([x] ++ ys) == (filterBad p [x]) ++ (filterBad p ys))

p2False p xs ys
  = (filterBad p (xs ++ ys) == (filterBad p xs) ++ (filterBad p ys))

p3False xs ys
  = (filterBad (> 0) (xs ++ ys) == (filterBad (> 0) xs) ++ (filterBad (> 0) ys))

lastList :: (Int -> Bool) -> [Int] -> [Int]
lastList _ [] = []
lastList p [x] = [x]
lastList p (x:xs) =
  case p x of
    True -> x : (lastList p xs)
    _ -> []

p4False p xs ys
  = (lastList p (xs ++ ys) == (lastList p xs) ++ (lastList p ys))
