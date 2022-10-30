module Sets3 where

import Data.Set

{-@ predicate In X Xs = Set_mem X (listElts Xs) @-}

{-@ isin :: x:_ -> ys:_ -> {v:Bool | v <=> In x ys }@-}
isin _ [_] = False
isin x (y:ys)
  | x == y    = True
  | otherwise = x `isin` ys
isin _ []     = False