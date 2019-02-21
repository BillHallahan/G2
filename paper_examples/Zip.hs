module Zip where

import Prelude hiding (zip)

-- Example from Section 2.4 in the paper.
-- The refinement on zip has an error, discoverable by calling G2.

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ die :: {x : String | false} -> a@-}
die :: String -> a
die x = error x

{-@ zip :: xs:[a] -> {ys:[b] | size xs > 0 => size ys > 0} -> [(a, b)] @-}
zip :: [a] -> [b] -> [(a, b)]
zip [] [] = []
zip (x:xs) (y:ys) = (x, y):zip xs ys
zip _ _ = die "Bad call to zip."
