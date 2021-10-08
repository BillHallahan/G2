{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data List = Cons Bool List | Nil

{-@ main :: List -> Int -> { b:Bool | b } @-}
main :: List -> Int -> Bool
main xs n =
    case while xs  cond loop (n, 0, 0) of
        (n', x, m) -> if n' > 0 then 0 <= m && m < n' else True

while :: List -> (a -> Bool) -> (List -> a -> a) -> a -> a
while xs pred body x =
    if pred x then while (listTail xs) pred body (body xs x) else x

{-@ cond :: (Int, Int, Int) -> Bool @-}
cond :: (Int, Int, Int) -> Bool
cond (n, x, m) = x < n

{-@ loop :: List -> (Int, Int, Int) -> (Int, Int, Int) @-}
loop :: List -> (Int, Int, Int) -> (Int, Int, Int)
loop xs (n, x, m) =
    if isTrueCons xs
        then (n, x + 1, x)
        else (n, x + 1, m)

isCons :: List -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List -> List
listTail (Cons _ ys) = ys
listTail _ = Nil