module List1 where

prop1 :: [Int] -> Bool
prop1 xs = [] ++ xs == xs

prop2 :: [Int] -> Bool
prop2 xs = xs ++ [] == xs

prop3 :: [Int] -> [Int] -> Bool
prop3 (_:_) _ = True
prop3 xs ys = xs ++ ys == ys