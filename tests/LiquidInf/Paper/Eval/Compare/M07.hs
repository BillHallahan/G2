{-@ LIQUID "--no-termination" @-}

module M7 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> n:{ n:Int | n >= 0} -> { b:Bool | b } @-}
main :: List Bool -> Int -> Bool
main xs n =
    case while xs (0, n, 0, 0) of
        (i', n', a', b') -> a' + b' == 3 * n' 

while :: List Bool -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
while xs (i, n, a, b) =
    if i < n
        then while (listTail xs) (if isTrueCons xs
                                        then (i + 1, n, a + 1, b + 2)
                                        else (i + 1, n, a + 2, b + 1))
        else (i, n, a, b)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil