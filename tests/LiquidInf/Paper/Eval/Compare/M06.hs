{-@ LIQUID "--no-termination" @-}

module M6 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> Bool
main xs ys =
    case while1 xs ys cond1 loop1 (1, 0, 0, 0) of
        (w', z', x', y') -> x' == y'

while1 :: List Bool -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> a -> a) -> a -> a
while1 xs ys pred body x =
    if pred xs x then while1 (listTail xs) (listTail ys) pred body (body (listListHead ys) x) else x

while2 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while2 ys pred body x =
    if pred ys x then while2 (listTail ys) pred body (body x) else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 ys _ = isCons ys

{-@ loop1 :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 ys (w, z, x, y) =
    let
        (x', y') = while2 ys cond2 (loop2 w z) (x, y)
    in
    (x' + y' + 1, x' + y', x', y')

{-@ cond2 :: List Bool -> (Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int) -> Bool
cond2 ys _ = isCons ys

{-@ loop2 :: Int -> Int -> (Int, Int) -> (Int, Int) @-}
loop2 :: Int -> Int -> (Int, Int) -> (Int, Int)
loop2 w z (x, y) =
    (if w `mod` 2 == 1 then x + 1 else x, if z `mod` 2 == 0 then y + 1 else y)

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