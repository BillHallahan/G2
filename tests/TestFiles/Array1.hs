module Array1 where

import GHC.Arr

buildArray1 :: (Int, Int, Int, Int, Int)
buildArray1 = let arr = listArray (3, 7) [3, 4, 2, 1, 9] in (arr ! 3, arr ! 4, arr ! 5, arr ! 6, arr ! 7)

buildArray2 :: (Int, Int, Int, Int, Int)
buildArray2 = let arr = array (3, 7) [(7, 11), (3, 4), (5, 8), (4, 7), (6, 1221)] in (arr ! 3, arr ! 4, arr ! 5, arr ! 6, arr ! 7)