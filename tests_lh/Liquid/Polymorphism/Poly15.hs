module Combined (call) where

data Map k a = Assocs [(k, a)]

call :: Int
call = g (f 1)

{-@ f :: k -> Map k Bool @-}
f :: k -> Map k Bool
f k = Assocs [(k, True)]

{-@ g :: Map k {x:Bool | x} -> Int @-}
g :: Map k Bool -> Int
g _ = 1
