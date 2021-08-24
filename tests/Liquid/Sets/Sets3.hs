module Sets3 where

import Data.Set hiding (filter)
import Prelude hiding (filter)

{-@ type ListSub a X = {v:[a]| Set_sub (listElts v) (listElts X)} @-}

{-@ filter   :: (Int -> Bool) -> xs:[Int]  -> v:ListSub Int xs @-}
filter :: (Int -> Bool) -> [Int] -> [Int]
filter _ []   = []
filter f (x:xs)
  | f x       = x : xs'
  | otherwise = 1:xs'
  where
    xs'       = filter f xs

alwaysTrue :: Int -> Bool
alwaysTrue _ = True

isPos :: Int -> Bool
isPos x = x > 0