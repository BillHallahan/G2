{-@ LIQUID "--no-termination" @-}

module Sets8 (prop) where

import Data.Set

{-@ type True = {v:Bool | v} @-}

{-@ prop  :: [Int] -> True @-}
prop :: [Int] -> Bool
prop xs = elts xs == elts xs'
  where
    (_, xs') = f xs

{-@ f            :: [Int] -> ([Int], [Int]) @-}
f            :: [Int] -> ([Int], [Int])
f xs       = ([], xs)

{-@ elts        :: xs:[Int] -> {ys:Set Int | ys == listElts xs} @-}
elts        :: [Int] -> Set Int
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

