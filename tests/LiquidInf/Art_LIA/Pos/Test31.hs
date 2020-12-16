{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}


module Combined ( List, k) where

import Data.List (minimumBy)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

data List a = Emp
            | C a
              deriving (Eq, Ord, Show)

callDie :: Int -> Int
callDie _ = die ""

{-@ k :: List Int -> [{v:Int | 0 <= v && v < 2}] -> {v:Int | 0 <= v && v < 2} @-}
k   :: List Int -> [Int] -> Int
k ps cs =
  case m (\_ -> n cs) ps of
      C k -> k
      Emp -> 1

n   :: [Int] -> Int
n centers = minimumBy (\_ _ -> LT) centers

m :: (a -> b) -> List a -> List b
m f Emp        = Emp
m f (C x) = C (f x)