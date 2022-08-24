{-@ LIQUID "--no-termination" @-}

module M22 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b:Bool | b } @-}
main :: Peano -> Bool
main xs = case while xs cond loop (0, 0, 0, 0) of
            (x', y', z', k') -> x' == y' && y' == z'

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: t1:{ t1:(Int, Int, Int, Int) |    x_Tuple41 t1 == x_Tuple42 t1 && x_Tuple42 t1 == x_Tuple43 t1 && x_Tuple44 t1 == 3 * x_Tuple42 t1 }
         -> t2:{ t2:(Int, Int, Int, Int) |    x_Tuple41 t2 == x_Tuple42 t2 && x_Tuple42 t2 == x_Tuple43 t2 && x_Tuple44 t2 == 3 * x_Tuple42 t2 } @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (x, y, z, k) =
    ( if k `mod` 3 == 0 then x + 1 else x
    , y + 1
    , z + 1
    , (if k `mod` 3 == 0 then x + 1 else x) + (y + 1) + (z + 1))


isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil

