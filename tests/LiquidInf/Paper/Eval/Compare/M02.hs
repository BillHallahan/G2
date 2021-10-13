{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b:Bool | b } @-}
main :: Peano -> Bool
main xs =
    case while xs cond loop (1 - 0, 0, 0, 0) of
        (z, x, y, w) -> x == y

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (z, x, y, w) =
    ( z + x + y + w
    , if (z + x + y + w) `mod` 2 == 1 then x + 1 else x
    , y + 1
    , w + 2)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil