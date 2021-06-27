module Append (prop_append1, prop_append2) where

import qualified Data.Set as S


{-@ prop_append1 :: xs:[Int] -> ys:[Int] -> { v:[Int] | Set_sub (listElts xs) (listElts v)} @-}
prop_append1 :: [Int] -> [Int] -> [Int]
prop_append1 xs ys = append xs ys

{-@ prop_append2 :: xs:[Int] -> ys:[Int] -> { v:[Int] | Set_sub (listElts ys) (listElts v)} @-}
prop_append2 :: [Int] -> [Int] -> [Int]
prop_append2 xs ys = append xs ys

append []     ys = ys
append (x:xs) ys = x : append xs ys