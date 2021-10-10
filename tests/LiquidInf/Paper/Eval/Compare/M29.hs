{-@ LIQUID "--no-termination" @-}

module M29 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> Bool
main xs ys =
    case while1 xs ys cond1 loop1 (1, 1, 2, 2, 3, 3) of
        (a', b', c', d', x', y') -> a' + c' == b' + d'

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

{-@ cond1 :: List Bool -> (Int, Int, Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int, Int, Int) -> Bool
cond1 xs (a, b, c, d, x, y) = isCons xs

{-@ loop1 :: List Bool -> (Int, Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int, Int) @-}
loop1 :: List Bool -> (Int, Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int, Int)
loop1 ys (a, b, c, d, x, y) =
    let
        (b', c') = while2 ys cond2 loop2 (b, c) 
    in
    ( if (x + y) `mod` 2 == 0 then a + 1 else a - 1
    , b'
    , c'
    , if (x + y) `mod` 2 == 0 then d + 1 else d
    , x
    , y)

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