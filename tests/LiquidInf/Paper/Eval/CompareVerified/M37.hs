{-@ LIQUID "--no-termination" @-}

module M2 (main) where

data List = Cons Bool List | Nil

{-@ main :: List -> Int -> { b:Bool | b } @-}
main :: List -> Int -> Bool
main xs n =
    case while xs n (0, 0) of
        (x, m) -> if n > 0 then 0 <= m && m < n else True

{-@ while :: List
		  -> n:Int
		  -> ({ x:Int | 0 <= x && (n > 0 => x <= n)}, { m:Int | 0 <= m && (n > 0 => m < n)})
		  -> (Int, { m:Int | 0 <= m && (n > 0 => m < n)}) @-}
while :: List -> Int -> (Int, Int) -> (Int, Int)
while xs n (x, m) =
    if x < n
        then while (listTail xs) n
                            (if isTrueCons xs
                                then (x + 1, x)
                                else (x + 1, m))
        else (x, m)

isCons :: List -> Bool
isCons (Cons _ _) = True
isCons _ = False

isTrueCons :: List -> Bool
isTrueCons (Cons x _) = x
isTrueCons _ = False

listTail :: List -> List
listTail (Cons _ ys) = ys
listTail _ = Nil