{-@ LIQUID "--no-termination" @-}

module M43 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Int -> Int -> { b:Bool | b } @-}
main :: Peano -> Int -> Int -> Bool
main _ x y | x == y = True
main xs x y = case while xs cond loop (x, y, 0, y) of
            (x', y', i', t') -> y' >= t'

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (x, y, i, t) = (x, if x > 0 then y + x else y, i, t)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil