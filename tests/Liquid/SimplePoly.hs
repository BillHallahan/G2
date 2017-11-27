module SimplePoly where

data Pair a b = Pair a b

{-@ snd2Int :: x:Int -> {y:Int | x /= y} -> {z:Int | y /= z} @-}
snd2Int :: Int -> Int -> Int
snd2Int x y = snd2 x y

snd2 :: a -> b -> b
snd2 _ x = x

{-@ sumPair :: x:Pair Int Int -> {v:Int | pfst x <= v && psnd x <= v} @-}
sumPair :: Pair Int Int -> Int
sumPair (Pair x y) = x + y

{-@ measure pfst @-}
pfst :: Pair a b -> a
pfst (Pair x _) = x

{-@ measure psnd @-}
psnd :: Pair a b -> b
psnd (Pair _ y) = y

switchInt :: Pair Int Int -> Pair Int Int
switchInt x = switch x

{-@ switch :: x:Pair a a -> {v:Pair a a | pfst x /= psnd v} @-} 
switch :: Pair a a -> Pair a a
switch (Pair x y) = Pair y x
