{-@ LIQUID "--no-termination" @-}

module M44 (main) where

{-@ main :: Int -> Int -> { b:Bool | b } @-}
main :: Int -> Int -> Bool
main k flag =
	case while (cond k) (loop flag (if flag == 1 then 1 else 2) k) (0, 0) of
        (i', j') -> if flag == 1 then j' == i' else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: Int -> (Int, Int) -> Bool @-}
cond :: Int -> (Int, Int) -> Bool
cond k (i, j) = i <= k

{-@ loop :: flag:Int
         -> n:{ n:Int | flag == 1 <=> n == 1 }
         -> k:Int
         -> pre:{ t:(Int, Int) | (n == 1 => x_Tuple21 t == x_Tuple22 t) }
         -> { t:(Int, Int) | (n == 1 => x_Tuple21 t == x_Tuple22 t) } @-}
loop :: Int -> Int -> Int -> (Int, Int) -> (Int, Int)
loop flag n k (i, j) = (i + 1, j + n)
