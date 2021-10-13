{-@ LIQUID "--no-termination" @-}

module M29 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> List (List Bool) -> Int -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> List (List Bool) -> Int -> Bool
main xs ys zs k =
    case while1 xs ys zs cond1 loop1 (k, k, 0, 0) of
        (k', z', x', y') -> x' == y'

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
cond1 xs _ = isCons xs

{-@ loop1 :: List Bool -> List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: List Bool -> List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 ys zs (k, z, x, y) =
    let
        (k', z', x', y', c') = while2 ys cond2 loop2 (k, z, x, y, 0)
        (x'', y'') = while2 zs cond3 loop3 (x', y')
    in
    (k', k' + y'', x'', y'')

{-@ cond2 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool
cond2 xs _ = isCons xs

{-@ loop2 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop2 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop2 (k, z, x, y, c) =
    if z == k + y - c then (k, z, x + 1, y + 1, c + 1) else (k, z, x + 1, y - 1, c + 1)

{-@ cond3 :: List Bool -> (Int, Int) -> Bool @-}
cond3 :: List Bool -> (Int, Int) -> Bool
cond3 xs _ = isCons xs

{-@ loop3 :: (Int, Int) -> (Int, Int) @-}
loop3 :: (Int, Int) -> (Int, Int)
loop3 (x, y) = (x - 1, y - 1)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

listHead :: List (List Bool) -> List Bool
listHead (Cons x _) = x
listHead _ = Nil

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil