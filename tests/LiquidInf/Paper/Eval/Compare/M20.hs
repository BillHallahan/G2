{-@ LIQUID "--no-termination" @-}

module M20 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Int -> x:Int -> y:Int -> k:{ k:Int | x + y == k } -> i:Int -> n:Int -> { b:Bool | b } @-}
main :: List Int -> Int -> Int -> Int -> Int -> Int -> Bool
main xs x y k i n =
    case while xs k n i (x, y, 0, 0) of
        (x', y', j', m') -> x' + y' == k && (if n > 0 then 0 <= m' && m' < n else True)

{-@ while :: List Int -> Int -> Int -> Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
while :: List Int -> Int -> Int -> Int -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
while xs k n i (x, y, j, m) =
    if j < n then while (listTail xs) k n i
                ( if j == i then x + 1 else x - 1
                , if j == i then y - 1 else y + 1
                , j + 1
                , if intHead xs >= 0 then j else m)
             else (x, y, j, m)

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