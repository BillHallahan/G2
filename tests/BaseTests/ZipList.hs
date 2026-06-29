module ZipList where

-- Testing that multi-line imports work with state
-- validation.
import Data.Maybe (); import Control.Applicative

callApp :: ZipList Int -> ZipList Int
callApp = (<*>) funcList

funcList :: ZipList (Int -> Int)
funcList = ZipList $ map (+) [1..]
