{-@ LIQUID "--no-termination" @-}

module M46 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b : Bool | b } @-}
main :: Peano -> Bool
main xs = case while xs cond loop (1, 0, 0, 0) of
                (w', z', x', y') -> x' <= 1

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Int, Int, Int, Int) -> Bool @-}
cond :: Peano -> (Int, Int, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (w, z, x, y) =
    ( if w `mod` 2 == 1 then w + 1 else w
    , if z `mod` 2 == 0 then z + 1 else z
    , if w `mod` 2 == 1 then x + 1 else x
    , if z `mod` 2 == 0 then y + 1 else y)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil