{-@ LIQUID "--no-termination" @-}

module M21 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Int -> n:{ n:Int | n > 0 && n < 10} -> { b:Bool | b } @-}
main :: List Int -> Int -> Bool
main xs n =
    case while xs 4000 2000 n (0, 0) of
        (i', k') -> k' > n

{-@ while :: List Int -> Int -> Int -> Int -> (Int, Int) -> (Int, Int) @-}
while :: List Int -> Int -> Int -> Int -> (Int, Int) -> (Int, Int)
while xs c1 c2 n (i, k) =
    if i < n
        then while (listTail xs) c1 c2 n
                    (let
                        v = if intHead xs `mod` 2 == 0 then 0 else 1
                    in
                    (i + 1, if v == 0 then k + c1 else k + c2))
        else (i, k)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

intHead :: List Int -> Int
intHead (Cons x _) = x
intHead _ = 0

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil