{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> List (List Bool) -> Bool
main xs ys zs =
    case while xs ys zs cond loop (0, 0) of
        (x, y) -> x < 4 || y > 2

while :: List Bool -> List (List Bool) -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> List Bool -> a -> a) -> a -> a
while xs ys zs pred body x =
    if pred xs x then while (listTail xs) (listTail ys) (listTail zs) pred body (body (listListHead ys) (listListHead zs) x) else x

{-@ cond :: List Bool -> (Int, Int) -> Bool @-}
cond :: List Bool -> (Int, Int) -> Bool
cond ys _ = isCons ys

{-@ loop :: List Bool -> List Bool -> (Int, Int) -> (Int, Int) @-}
loop :: List Bool -> List Bool -> (Int, Int) -> (Int, Int)
loop ys zs (x, y) =
    if isTrueCons ys
        then (x + 1, y + 100)
        else (if isTrueCons zs
                    then (if x >= 4
                            then (x + 1, y + 1)
                            else (if x < 0 then (x, y - 1) else (x, y)))
                    else (x, y))

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listListHead :: List (List a) -> List a
listListHead (Cons x _) = x
listListHead _ = Nil

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil