{-@ LIQUID "--no-termination" @-}

module M12 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List Bool -> Int -> { b:Bool | b } @-}
main :: List Bool -> List Bool -> Int -> Bool
main xs ys flag =
    case while xs cond1 (loop1 flag) (0, 0, 0, 0) of
        (t', s', a', b') -> case while2 ys (if flag >= 0 then t' - 2 * s' + 2 else 1, 0)  of
                                        (x', y') ->  y' <= 4

while :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while ys pred body x = if pred ys x then while (listTail ys) pred body (body x) else x

{-@ while2 :: List Bool
           -> t:{ t:(Int, Int) | fst t <= 2 && snd t <= 4 }
           -> { t:(Int, Int) | snd t <= 4 } @-}
while2 :: List Bool -> (Int, Int) -> (Int, Int)
while2 xs (x, y) =
    if y <= x
        then while2 (listTail xs) (x, if isTrueCons xs then y + 1 else y + 2)
        else (x, y)

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 xs (t, s, a, b) = isTrueCons xs

{-@ loop1 :: Int
          -> t:{ t:(Int, Int, Int, Int) | (x_Tuple43 t == x_Tuple44 t)
                                        && (x_Tuple41 t <= 2 * x_Tuple42 t)
                                        && 0 <= x_Tuple43 t }
          -> { t:(Int, Int, Int, Int) | (x_Tuple43 t == x_Tuple44 t)
                                        && (x_Tuple41 t <= 2 * x_Tuple42 t)
                                        && 0 <= x_Tuple43 t } @-}
loop1 :: Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 flag (t, s, a, b) = (t + b + 1 + (if flag >= 0 then a else 0), s + a + 1, a + 1, b + 1)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil