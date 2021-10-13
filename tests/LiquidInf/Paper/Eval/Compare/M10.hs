{-@ LIQUID "--no-termination" @-}

module M5 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b:Bool | b } @-}
main :: Peano -> Bool
main xs = case while xs cond loop (True, False, 0, 0) of
            (w', z', x', y') -> x' == y'

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond :: Peano -> (Bool, Bool, Int, Int) -> Bool @-}
cond :: Peano -> (Bool, Bool, Int, Int) -> Bool
cond ys _ = isSucc ys

{-@ loop :: (Bool, Bool, Int, Int) -> (Bool, Bool, Int, Int) @-}
loop :: (Bool, Bool, Int, Int) -> (Bool, Bool, Int, Int)
loop (w, z, x, y) =
    ( if w then not w else w
    , if not z then not z else z
    , if w then x + 1 else x
    , if not z then y + 1 else y)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil