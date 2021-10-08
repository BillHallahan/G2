{-@ LIQUID "--no-termination" @-}

module M1 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b:Bool | b } @-}
main :: Peano -> Bool
main xs = case while xs cond loop (1, 1) of
            (x', y') -> y' >= 1

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Int, Int) -> (Int, Int) @-}
loop :: (Int, Int) -> (Int, Int)
loop (x, y) =
    let
        t1 = x
        t2 = y
    in
    (t1 + t2, t1 + t2)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil