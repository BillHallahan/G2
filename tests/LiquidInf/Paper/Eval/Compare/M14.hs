{-@ LIQUID "--no-termination" @-}

module M14 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> Int -> { b:Bool | b } @-}
main :: List Bool -> Int -> Bool
main xs m | m <= 0 = True
          | otherwise = 
                    case while xs (0, 1, m) of
                        (a', j', m') -> a' >= -m' && a' <= m'

while :: List Bool -> (Int, Int, Int) -> (Int, Int, Int)
while xs (a, j, m) =
    if j <= m then while (listTail xs) (if isTrueCons xs
                                            then (a + 1, j + 1, m)
                                            else (a - 1, j + 1, m))
              else (a, j, m)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil