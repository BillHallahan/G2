module Risers (c_risers) where

import Prelude hiding (length)

c_risers :: [Int] -> [[Int]]
c_risers xs = risers (0:xs)

risers           :: (Ord a) => [a] -> [[a]]
risers []        = []
risers [x]       = [[x]]
risers (x:y:etc)
  | x <= y       = (x:s) : ss
  | otherwise    = [x] : (s : ss)
    where
      (s, ss)    = safeSplit $ risers (y:etc)

safeSplit (x:xs) = (x, xs)
safeSplit _      = die "don't worry, be happy"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
