{-@ LIQUID "--no-termination" @-}

module M29 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> Bool
main xs ys =
    case while1 xs ys cond1 (\xs' -> loop1 xs' 3 3) (1, 1, 2, 2) of
        (a', b', c', d') -> a' + c' == b' + d'

while1 :: List Bool -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> a -> a) -> a -> a
while1 xs ys pred body x =
    if pred xs x
        then while1 (listTail xs) (listTail ys) pred body (body (listHead ys) x)
        else x

while2 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while2 xs pred body x =
    if pred xs x
        then while2 (listTail xs) pred body (body x)
        else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 xs (a, b, c, d) = isCons xs

{-@ loop1 :: List Bool -> Int -> Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: List Bool -> Int -> Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 ys x y (a, b, c, d) =
    let
        (b', c') = while2 ys cond2 loop2 (b, c) 
    in
    ( if (x + y) `mod` 2 == 0 then a + 1 else a - 1
    , b'
    , c'
    , if (x + y) `mod` 2 == 0 then d + 1 else d)

{-@ cond2 :: List Bool -> (Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int) -> Bool
cond2 xs _ = isCons xs

{-@ loop2 :: (Int, Int) -> (Int, Int) @-}
loop2 :: (Int, Int) -> (Int, Int)
loop2 (b, c) = (b - 1, c - 1)


isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

listHead :: List (List Bool) -> List Bool
listHead (Cons x _) = x
listHead _ = Nil

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil