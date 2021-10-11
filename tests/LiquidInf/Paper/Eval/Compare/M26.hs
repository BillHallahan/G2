{-@ LIQUID "--no-termination" @-}

module M26 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> List (List Bool) -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> List (List Bool) -> Bool
main xs ys zs =
    case while1 xs ys zs cond1 loop1 (1, 0, 0, 0) of
        (_, _, x', y') -> x' == y'

while1 :: List Bool -> List (List Bool) -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> List Bool -> a -> a) -> a -> a
while1 xs ys zs pred body x =
    if pred xs x
        then while1 (listTail xs) (listTail ys) (listTail zs) pred body (body (listHead ys) (listHead zs) x)
        else x

while2 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while2 xs pred body x =
    if pred xs x
        then while2 (listTail xs) pred body (body x)
        else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 xs (w, z, x, y) = isCons xs

{-@ loop1 :: List Bool -> List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: List Bool -> List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 ys zs (w, z, x, y) =
    let
        (x', y') = while2 ys cond2 (loop2 w z) (x, y)
        (w', z') = while2 zs cond3 (loop3 x' y') (w, z)
    in
    (w', z', x', y')

{-@ cond2 :: List Bool -> (Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int) -> Bool
cond2 xs (x, y) = isCons xs

{-@ loop2 :: Int -> Int -> (Int, Int) -> (Int, Int) @-}
loop2 :: Int -> Int -> (Int, Int) -> (Int, Int)
loop2 w z (x, y) = (if w `mod` 2 == 1 then x + 1 else x, if z `mod` 2 == 0 then y + 1 else y)

{-@ cond3 :: List Bool -> (Int, Int) -> Bool @-}
cond3 :: List Bool -> (Int, Int) -> Bool
cond3 xs (w, z) = isCons xs

{-@ loop3 :: Int -> Int -> (Int, Int) -> (Int, Int) @-}
loop3 :: Int -> Int -> (Int, Int) -> (Int, Int)
loop3 x y (w, z) = (x + y + 1, x + y)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

listHead :: List (List Bool) -> List Bool
listHead (Cons x _) = x
listHead _ = Nil

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil