module Tuples where

import Data.Monoid

addTupleElems :: (Int, Float, Double, Int, Int) -> (Int, Int)
addTupleElems (a, b, c, d, e) = case a + e of
  0 -> (24680, 13579)
  _ -> (12345, 67890)

oneTwo :: (Int, Int)
oneTwo = (1, 2)

applicativeTuple :: (Sum Int, Int) -> (Sum Int, Int)
applicativeTuple y = pure (\x -> x * 2) <*> y

monadTuple :: (Sum Int, Int) -> (Sum Int, Int)
monadTuple y@(z, _) = y >>= (\x -> (z, x + 7))