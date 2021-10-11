{-@ LIQUID "--no-termination" @-}

module M36 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List (List Bool) -> List Bool -> Int -> { b:Bool | b } @-}
main :: List Bool -> List (List Bool) -> List Bool -> Int -> Bool
main xs ys zs flag = case while1 xs ys cond1 loop1 (0, 0, 0, 0, 0) of
                        (k, w, x, y, z) -> case while2 zs cond4 (loop4 flag) (0, 0, 0, 0) of
                                                (a, b, c, d) -> w >= z && a - b == 0

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x =
    if pred x then while pred body (body x) else x

while1 :: List Bool -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> a -> a) -> a -> a
while1 xs ys pred body x =
    if pred xs x then while1 (listTail xs) (listTail ys) pred body (body (listListHead ys) x) else x

while2 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while2 xs pred body x =
    if pred xs x then while2 (listTail xs) pred body (body x) else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool
cond1 xs (k, w, x, y, z) = isCons xs

{-@ loop1 :: List Bool -> (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop1 :: List Bool -> (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop1 xs (k, w, x, y, z) =
    let
        (k', i') = while (cond2 w) loop2 (k, z)
        
        (x', y') = while2 xs cond3 loop3 ( z + (if z `mod` 2 == 1 then 1 else 0)
                                         , z - (if z `mod` 2 == 1 then 1 else 0))
    in
    (k', x' + y' + 1, x', y', z + 1)

{-@ cond2 :: Int -> (Int, Int) -> Bool @-}
cond2 :: Int -> (Int, Int) -> Bool
cond2 j (k, i) = i < j

{-@ loop2 :: (Int, Int) -> (Int, Int) @-}
loop2 :: (Int, Int) -> (Int, Int)
loop2 (k, i) = (k + 1, i +1)

{-@ cond3 :: List Bool -> (Int, Int) -> Bool @-}
cond3 :: List Bool -> (Int, Int) -> Bool
cond3 xs _ = isCons xs

{-@ loop3 :: (Int, Int) -> (Int, Int) @-}
loop3 :: (Int, Int) -> (Int, Int)
loop3 (x, y) = if x `mod` 2 == 0 then (x + 2, y - 2) else (x - 1, y - 1)

{-@ cond4 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond4 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond4 xs _ = isCons xs

{-@ loop4 :: Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop4 :: Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop4 flag (a, b, c, d) =
    (if flag >= 0 then a + 1 else a + c + 1, if flag >= 0 then b + 1 else b + d + 1, c + 1, d + 1)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

intHead :: List Int -> Int
intHead (Cons x _) = x
intHead _ = 0

listListHead :: List (List a) -> List a
listListHead (Cons x _) = x
listListHead _ = Nil

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil