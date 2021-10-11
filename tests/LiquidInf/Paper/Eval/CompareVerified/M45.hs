{-@ LIQUID "--no-termination" @-}

module M45 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> List Bool -> List (List Bool) -> Int -> { b:Bool | b } @-}
main :: List Bool -> List Bool -> List (List Bool) -> Int -> Bool
main xs ys zs flag =
    case while1 xs cond1 (loop1 flag) (0, 0, 0, 0) of
        (x, y, i, j) ->
            case while2 ys zs cond2 loop2 (if j >= i then y else y + 1, y, 0, 1) of
                (x', y', z', w') -> x' == y'

while1 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while1 xs pred body x =
    if pred xs x then while1 (listTail xs) pred body (body x) else x

while2 :: List Bool -> List (List Bool) -> (List Bool -> a -> Bool) -> (List Bool -> a -> a) -> a -> a
while2 xs ys pred body x =
    if pred xs x then while2 (listTail xs) (listTail ys) pred body (body (listListHead ys) x) else x

while3 :: List Bool -> (List Bool -> a -> Bool) -> (a -> a) -> a -> a
while3 xs pred body x =
    if pred xs x then while3 (listTail xs) pred body (body x) else x

{-@ cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond1 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond1 ys _ = isCons ys

{-@ loop1 :: Int
          -> t:{ t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t) 
                                        && x_Tuple43 t <= x_Tuple44 t}
          -> { t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t) 
                                      && x_Tuple43 t <= x_Tuple44 t} @-}
loop1 :: Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 flag (x, y, i, j) =
    (x + 1, y + 1, i + x + 1, j + y + 1 + (if flag > 0 then 1 else 0))

{-@ cond2 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond2 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond2 ys _ = isCons ys

{-@ loop2 :: List Bool
          -> t:{ t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t) 
                                        && x_Tuple43 t + 1 == x_Tuple44 t }
          -> { t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t)
                                      && x_Tuple43 t + 1 == x_Tuple44 t} @-}
loop2 :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop2 xs xyzw =
    while3 xs cond3 loop3 xyzw

{-@ cond3 :: List Bool -> (Int, Int, Int, Int) -> Bool @-}
cond3 :: List Bool -> (Int, Int, Int, Int) -> Bool
cond3 ys _ = isCons ys

{-@ loop3 :: t:{ t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t) 
                                        && x_Tuple43 t + 1 == x_Tuple44 t }
          -> { t:(Int, Int, Int, Int) | (x_Tuple41 t == x_Tuple42 t)
                                      && x_Tuple43 t + 1 == x_Tuple44 t} @-}
loop3 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop3 (x, y, z, w) =
    let
        x' = if w `mod` 2 == 1 then x + 1 else x
        y' = if z `mod` 2 == 0 then y + 1 else y
    in
    (x', y', x' + y', x' + y' + 1)

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