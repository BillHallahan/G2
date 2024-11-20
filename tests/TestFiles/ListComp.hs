module ListComp where

data Wheel = Wheel Int [Int]

list1 = list2 !! 1

list2 :: [Int]
list2 =
  [o | o <- [2,3..4]] 