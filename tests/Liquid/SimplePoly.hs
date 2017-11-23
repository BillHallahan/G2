module SimplePoly where

{-@ snd2Int :: x:Int -> {y:Int | x /= y} -> {z:Int | y /= z} @-}
snd2Int :: Int -> Int -> Int
snd2Int x y = snd2 x y

snd2 :: a -> b -> b
snd2 _ x = x