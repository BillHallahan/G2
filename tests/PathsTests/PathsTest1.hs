module PathsTest1 where

f xs = case xs of
    [] -> []
    [_] -> []
    (_:_) -> xs

test1 list = case f list of
    [] -> []
    _  -> list

len [] = 0
len (x:xs) = 1 + len xs

test2 list = case len list of 
    1 -> []
    _ -> list

test3 list = case [] of
    [] -> []
    _:_ -> list