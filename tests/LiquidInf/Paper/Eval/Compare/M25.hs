{-@ LIQUID "--no-termination" @-}

module M25 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> Bool
main xs ys =
    case while1 xs ys cond1 loop1 (0, 0, 0, 0) of
        (x, y, i, j) -> i >= j

while1 :: List Bool -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> a -> a) -> a -> a
while1 xs ys pred body x =
    if pred xs x then while1 (listTail xs) (listTail ys) pred body (body (listListHead ys) x) else x

while2 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while2 xs pred body x =
    if pred xs x then while2 (listTail xs) pred body (body x) else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 ys _ = isCons ys

{-@ loop1 :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 ys xyij =
    let
        (x', y', i', j') = while2 ys cond2 loop2 xyij
    in
    if i' >= j'
        then (x' + 1, y' + 1, i', j')
        else (x', y' + 1, i', j')

{-@ cond2 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond2 ys _ = isCons ys

{-@ loop2 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop2 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop2 (x, y, i, j) = if x == y then (x, y, i + 1, j) else (x, y, i, j + 1)

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