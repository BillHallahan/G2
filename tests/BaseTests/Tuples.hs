module Tuples where

addTupleElems :: (Int, Float, Double, Int, Int) -> (Int, Int)
addTupleElems (a, b, c, d, e) = case a + e of
  0 -> (24680, 13579)
  _ -> (12345, 67890)

oneTwo :: (Int, Int)
oneTwo = (1, 2)

