{-@ LIQUID "--no-termination" @-}

module M31 (main) where

data List a = Cons a (List a) | Nil

{-@ main :: List (List Int) -> Int -> Int -> (Int, Int) @-}
main :: List (List Int) -> Int -> Int -> (Int, Int)
main xs m n
    | m + 1 < n = while1 m n xs (0, 0)
    | otherwise = (0, 0)

{-@ while1 :: Int -> Int -> List (List Int) -> (Int, Int) -> (Int, Int) @-}
while1 :: Int -> Int -> List (List Int) -> (Int, Int) -> (Int, Int)
while1 m n xs (i, j) =
    if i < n
        then while1 m n (listTail xs)
                (let
                    (_, j') = while2 (listListHead xs) (cond2 m) (\b -> loop2 b m n) (i, 0)
                in
                (i + 4, j'))
        else (i, j)

while2 :: List Int -> (a -> Bool) -> (Int -> a -> a) -> a -> a
while2 xs pred body x = if pred x then while2 (listTail xs) pred body (body (intHead xs) x) else x

while3 :: (a -> Bool) -> (a -> a) -> a -> a
while3 pred body x = if pred x then while3 pred body (body x) else x

{-@ cond2 :: Int -> (Int, Int) -> Bool @-}
cond2 :: Int -> (Int, Int) -> Bool
cond2 m (i, j) = j < m

{-@ loop2 :: Int -> Int -> Int -> (Int, Int) -> (Int, Int) @-}
loop2 :: Int -> Int -> Int -> (Int, Int) -> (Int, Int)
loop2 b m n (i, j) =
    if b >= 0 
        then (case j >= 0 of
                True -> let _ = while3 (cond3 (j + 1)) loop3 0 in (i, j + 1)
                False -> die "bad")
        else (case n + j + 5 > i of
                True -> (i, j + 2)
                False -> die "bad")

{-@ cond3 :: Int -> Int -> Bool @-}
cond3 :: Int -> Int -> Bool
cond3 j k = k < j

{-@ loop3 :: Int -> Int @-}
loop3 :: Int -> Int
loop3 k = k + 1

{-@ die :: {v:String | false} -> a @-}
die str = error str

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