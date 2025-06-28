module List1 where

prop1 :: [()] -> Bool
prop1 xs = xs == xs

prop2 :: [Int] -> Bool
prop2 xs = [] ++ xs == xs

prop3 :: [Int] -> Bool
prop3 xs = xs ++ [] == xs

prop4 :: [Int] -> [Int] -> Bool
prop4 (_:_) _ = True
prop4 xs ys = xs ++ ys == ys

prop5 :: [Int] -> Int -> Bool
prop5 xs x = xs < xs ++ [x]

prop6 :: [Int] -> [Int] -> Bool
prop6 xs ys = xs <= xs ++ ys

prop6False :: [Int] -> [Int] -> Bool
prop6False xs ys = xs < xs ++ ys