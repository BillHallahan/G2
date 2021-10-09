{-@ LIQUID "--no-termination" @-}

module M44 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Peano -> Int -> { b:Bool | b } @-}
main :: Peano -> Peano -> Int -> Bool
main xs ys flag = case while xs cond1 loop1 (flag, if flag == 1 then 0 else 1, 1) of
                (flag', i', j') -> case while ys cond2 loop2 (flag, 0, 0, i', j') of
                                            (_, a', b', _, _) -> if flag == 1 then a' == b' else True

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while xs pred body x = if pred xs x then while (peanoTail xs) pred body (body x) else x

{-@ cond1 :: Peano -> (Int, Int, Int) -> Bool @-}
cond1 :: Peano -> (Int, Int, Int) -> Bool
cond1 xs (flag, i, j) = isSucc xs

{-@ loop1 :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop1 :: (Int, Int, Int) -> (Int, Int, Int)
loop1 (flag, i, j) = (flag, i + 2, if (i + 2) `mod` 2 == 0 then j + 2 else j + 1)

{-@ cond2 :: Peano -> (Int, Int, Int, Int, Int) -> Bool @-}
cond2 :: Peano -> (Int, Int, Int, Int, Int) -> Bool
cond2 xs (flag, a, b, i, j) = isSucc xs

{-@ loop2 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop2 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop2 (flag, a, b, i, j) = (flag, a + 1, b + j - i, i, j)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil