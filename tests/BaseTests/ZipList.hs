module ZipList where

import Control.Applicative

callApp :: ZipList Int -> ZipList Int
callApp = (<*>) funcList

funcList :: ZipList (Int -> Int)
funcList = ZipList $ map (+) [1..]