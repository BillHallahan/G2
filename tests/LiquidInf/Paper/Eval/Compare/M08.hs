{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data List = Cons Bool List | Nil

{-@ main :: List -> List -> List -> { b:Bool | b } @-}
main :: List -> List -> List -> Bool
main xs ys zs =
    case while xs ys zs cond loop (0, 0) of
        (x, y) -> x < 4 || y > 2

while :: List -> List -> List -> (List -> a -> Bool) -> (List -> List -> a -> a) -> a -> a
while xs ys zs pred body x =
    if pred xs x then while (listTail xs) (listTail ys) (listTail zs) pred body (body ys zs x) else x

{-@ cond :: List -> (Int, Int) -> Bool @-}
cond :: List -> (Int, Int) -> Bool
cond ys _ = isCons ys

{-@ loop :: List -> List -> (Int, Int) -> (Int, Int) @-}
loop :: List -> List -> (Int, Int) -> (Int, Int)
loop ys zs (x, y) =
    if isTrueCons ys
        then (x + 1, y + 100)
        else (if isTrueCons zs
                    then (if x >= 4
                            then (x + 1, y + 1)
                            else (if x < 0 then (x, y - 1) else (x, y)))
                    else (x, y))

isCons :: List -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List -> List
listTail (Cons _ ys) = ys
listTail _ = Nil