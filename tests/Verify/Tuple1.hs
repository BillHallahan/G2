module Tuple1 where

import Prelude hiding (foldr)
import Data.Coerce

(<|>) :: (Int, ()) -> (Int, ()) -> (Int, ())
(x, ()) <|> (y, ()) = (x + y, ())

p1 ::[(Int, ())] -> Bool
p1 xs = foldr 0 xs == foldr 0 xs

foldr :: Int -> [(Int, ())] -> (Int, ())
foldr z = go
          where
            go []     = ( 0, ())
            go (y:ys) = y  <|> go ys