module PathsTest1 where

f xs = case xs of
    [] -> []
    [_] -> []
    (_:_) -> xs

test1 list = case f list of
    [] -> []
    _  -> list