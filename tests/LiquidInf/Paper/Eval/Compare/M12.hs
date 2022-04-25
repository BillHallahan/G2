{-@ LIQUID "--no-termination" @-}

module M12 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List Bool -> Int -> { b:Bool | b } @-}
main :: List Bool -> List Bool -> Int -> Bool
main xs ys flag =
    case while xs cond1 loop1 (flag, 0, 0, 0, 0) of
        (flag', t', s', a', b') -> case while2 ys cond2 loop2 (if flag >= 0 then t' - 2 * s' + 2 else 1, 0)  of
                                        (x', y') ->  y' <= 4

while :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (listTail ys) pred body (body x) else x

while2 :: List Bool -> (a -> Bool) -> (List Bool -> a -> a) -> a -> a
while2 ys pred body x = if pred x then while2 (listTail ys) pred body (body ys x) else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int, Int) -> Bool
cond1 xs (flag, t, s, a, b) = isTrueCons xs

{-@ loop1 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop1 :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop1 (flag, t, s, a, b) = (flag, t + b + 1 + (if flag >= 0 then a + 1 else 0), s + a + 1, a + 1, b + 1)

{-@ cond2 :: (Int, Int) -> Bool @-}
cond2 :: (Int, Int) -> Bool
cond2 (x, y) = y <= x

{-@ loop2 :: List Bool -> (Int, Int) -> (Int, Int) @-}
loop2 :: List Bool -> (Int, Int) -> (Int, Int)
loop2 xs (x, y) = (x, if isTrueCons xs then y + 1 else y + 2)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil