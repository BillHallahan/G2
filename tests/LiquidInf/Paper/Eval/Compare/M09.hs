{-@ LIQUID "--no-termination" @-}

module M9 (main) where

data Peano = Succ Peano | Nil

{-@ main :: Peano -> Peano -> Int -> (Int, Int, Int, Int) @-}
main :: Peano -> Peano -> Int -> (Int, Int, Int, Int)
main xs ys pvlen =
    case while xs cond1 loop1 0 of
            i' ->
                case while ys cond2 loop2 (0, 0) of
                    (i'', k') -> breakWhile (i'', k', 0, i'') 

while :: Peano -> (Peano -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (peanoTail ys) pred body (body x) else x

breakWhile :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
breakWhile (i, k, j, n) =
    case k >= 0 of
            True -> if j + 1 < n
                        then breakWhile (i - 1, k - 1, j + 1, n)
                        else (i - 1, k - 1, j + 1, n)
            False -> die "bad!"

{-@ cond1 :: Peano -> Int -> Bool @-}
cond1 :: Peano -> Int -> Bool
cond1 ys _ = isSucc ys

{-@ loop1 :: Int -> Int @-}
loop1 :: Int -> Int
loop1 i = i + 1

{-@ cond2 :: Peano -> (Int, Int) -> Bool @-}
cond2 :: Peano -> (Int, Int) -> Bool
cond2 ys _ = isSucc ys

{-@ loop2 :: (Int, Int) -> (Int, Int) @-}
loop2 :: (Int, Int) -> (Int, Int)
loop2 (i, k) = (i + 1, k + 1)

isSucc :: Peano -> Bool
isSucc (Succ _) = True
isSucc _ = False

peanoTail :: Peano -> Peano
peanoTail (Succ ys) = ys
peanoTail _ = Nil

{-@ die :: {v:String | false} -> a @-}
die str = error str
