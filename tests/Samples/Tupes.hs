module Tupes where

firstPick :: (Int, Float, Double, Char, String) -> (Int, Int)
firstPick (a, b, c, d, e) = case a of
  0 -> (24680, 13579)
  _ -> (12345, 67890)

oneTwo :: (Int, Int)
oneTwo = (1, 2)

