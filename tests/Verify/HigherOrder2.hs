module HigherOrder2 where

prop :: (Int -> Int) -> Bool
prop u = r (u <**> True) == u 0

(<**>) :: (Int -> Int) -> Bool -> [Int -> Int]
u <**> xs =  case xs of
                        False  -> []
                        True -> (\x -> u x):u <**> False

r :: [Int -> Int] -> Int
r f =  case f of
            []  -> 0
            h : _ -> h 0
