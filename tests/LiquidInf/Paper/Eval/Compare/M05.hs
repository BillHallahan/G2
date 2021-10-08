{-@ LIQUID "--no-termination" @-}

module M5 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Int -> { b:Bool | b } @-}
main :: Peano -> Int -> Bool
main xs flag = case while xs cond loop (flag, 0, 0, 0, 0) of
            (flag', x', y', j', i') -> j' >= i'

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop (flag, x, y, j, i) = (flag, x + 1, y + 1, j + y + (if flag >= 100 then 1 else 0), i + x)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil