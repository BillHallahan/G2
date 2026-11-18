module List8 where

import Prelude hiding (filter)

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p [x] = [x]
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

rev :: [a] -> [a]
rev [] = []
rev (x:xs) = rev xs ++ [x]

p1False p xs = ( (filter p xs) == filter p (rev xs))
