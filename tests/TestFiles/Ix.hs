module Ix where

import Data.Ix

ixRange1 :: Int -> Int -> [Int]
ixRange1 x y = range (x, y)