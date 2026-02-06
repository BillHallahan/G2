module HasCallStack where

import GHC.Stack

f :: HasCallStack => Int -> Int
f x | x >= 0 = x
    | otherwise = error "negative x"