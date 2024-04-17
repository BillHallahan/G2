{-@ LIQUID "--no-termination" @-}

module M1 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> { b:Bool | b } @-}
main :: Peano -> Bool
main xs = case while xs cond1 loop1 (0, 0) of
            (x', y') -> case while2 (x', y', 0) of
                                (x'', y'', n'') -> y'' == n''

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

{-@ cond1 :: Peano -> (Int, Int) -> Bool @-}
cond1 :: Peano -> (Int, Int) -> Bool
cond1 ys _ = isSucc ys

{-@ loop1 :: (Int, Int) -> (Int, Int) @-}
loop1 :: (Int, Int) -> (Int, Int)
loop1 (x, y) = (x + 1, y + 1)

{-@ while2 :: (Int, Int, Int) -> { t:(Int, Int, Int) | not (x_Tuple31 t /= x_Tuple33 t) } @-}
while2 :: (Int, Int, Int) -> (Int, Int, Int)
while2 (x, y, n) = if x /= n then while2 (x - 1, y - 1, n) else (x, y, n)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil