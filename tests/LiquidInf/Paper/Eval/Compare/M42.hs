{-@ LIQUID "--no-termination" @-}

module M42 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Int -> { b:Bool | b } @-}
main :: Peano -> Int -> Bool
main xs flag = case while xs cond loop (flag, if flag >= 0 then 0 else 1, 1, 1) of
                (flag', a', x', y') -> (if flag >= 0 then a' + 1 else a') `mod` 2 == 1

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while xs pred body x = if pred xs x then while (peanoTail xs) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int) -> Bool
cond xs _ = isSucc xs

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (flag, a, x, y) =
    let
        a' = if flag >= 0 then x + y else x + y + 1
        x' = if flag >= 0 then x + 1 else x
        y' = if flag >= 0 then y else y + 1
    in
    ( flag
    , a'
    , if a' `mod` 2 == 1 then x' else x' + 1
    , if a' `mod` 2 == 1 then y' + 1 else y')

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil