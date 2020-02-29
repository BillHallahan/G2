module Head (usesHead) where

import Prelude hiding (head)

{-@ die :: {v:String | false} -> a @-}
die = error

usesHead :: Int
usesHead = head [1, 2, 3]

head :: [a] -> a
head (x:_) = x
head _ = die "head: Bad call"