module MeasErr where

{-@ measure m  :: (Int, Int) -> Int @-}
m :: (Int, Int) -> Int
m (_, b)  = b

{-@ f :: {y:(Int, Int) | 0 = m y} -> Int @-}
f :: (Int, Int) -> Int
f _ = 0
