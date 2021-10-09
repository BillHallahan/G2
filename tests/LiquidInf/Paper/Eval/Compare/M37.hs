{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data List = Cons Bool List | Nil

{-@ main :: List -> Int -> { b:Bool | b } @-}
main :: List -> Int -> Bool
main xs n =
    case while xs (n, 0, 0) of
        (n', x, m) -> if n' > 0 then 0 <= m && m < n' else True

while :: List -> (Int, Int, Int) -> (Int, Int, Int)
while xs (n, x, m) =
    if x < n
        then while (listTail xs)
                            (if isTrueCons xs
                                then (n, x + 1, x)
                                else (n, x + 1, m))
        else (n, x, m)

isCons :: List -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List -> List
listTail (Cons _ ys) = ys
listTail _ = Nil