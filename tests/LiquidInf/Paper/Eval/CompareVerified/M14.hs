{-@ LIQUID "--no-termination" @-}

module M14 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List Bool -> Int -> { b:Bool | b } @-}
main :: List Bool -> Int -> Bool
main xs m | m <= 0 = True
          | otherwise = 
                    case while xs m (0, 1) of
                        (a', j') -> a' >= -m && a' <= m

{-@ while :: List Bool
		  -> m:{ m:Int | m > 0}
		  -> t:{ t:(Int, { j:Int | j <= m + 1 }) | fst t > -snd t && fst t < snd t }
		  -> ({ a:Int | a >= - m && a <= m }, Int) @-}
while :: List Bool -> Int -> (Int, Int) -> (Int, Int)
while xs m (a, j) =
    if j <= m then while (listTail xs) m (if isTrueCons xs
                                            then (a + 1, j + 1)
                                            else (a - 1, j + 1))
              else (a, j)

isCons :: List a -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List Bool -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List a -> List a
listTail (Cons _ ys) = ys
listTail _ = Nil