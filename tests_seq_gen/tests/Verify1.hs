module Verify1 where

app :: [a] -> [a] -> [a]
app [] ys = ys
app (x:xs) ys = x:app xs ys

eq :: Eq a => [a] -> [a] -> Bool
eq [] [] = True
eq (x:xs) (y:ys) = x == y && xs `eq` ys
eq _ _ = False

myTake :: Int -> [a] -> [a]
myTake n _ | n <= 0 = []
myTake n [] = []
myTake n (x:xs) = x:myTake (n - 1) xs
