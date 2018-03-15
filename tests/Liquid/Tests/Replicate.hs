module Replicate where

data List = Emp
            | (:+:) Int List
              deriving (Eq, Ord, Show)

replicate :: Int -> List
{-@ replicate :: Int -> {x: List | false} @-}
replicate n = loop 0
  where loop 0 = Emp
        loop t = Emp
