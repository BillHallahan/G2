{-@ LIQUID "--no-termination" @-}

module M19 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Bool -> { b:Bool | b } @-}
main :: Peano -> Bool -> Bool
main xs flag =
    case while xs cond loop (flag, 2, 0) of
        (_, j, k) -> if k /= 0 then j == 2 * k + 2 else True

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while xs pred body x = if pred xs x then while (peanoTail xs) pred body (body x) else x

{-@ cond :: Peano -> (Bool, Int, Int) -> Bool @-}
cond :: Peano -> (Bool, Int, Int) -> Bool
cond xs _ = isSucc xs

{-@ loop :: (Bool, Int, Int) -> (Bool, Int, Int) @-}
loop :: (Bool, Int, Int) -> (Bool, Int, Int)
loop (flag, j, k) = if flag then (flag, j + 4, k) else (flag, j + 2, k + 1)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil