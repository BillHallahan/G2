module HigherOrder where

data List = Cons Bool List | EmptyList

f :: (List -> List) -> List -> Bool
f g l = case g l of
    Cons True l -> True
    -- _ -> False
    Cons False l -> False
    EmptyList -> True

h :: (Int -> Int) -> Bool
h g = g 0 <= g 1