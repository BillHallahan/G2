module MaybeFuncHigherOrder where

f :: (Int -> Maybe (Int -> Int)) -> Int
f g =
    case g 1 of
        Just h -> case g (one ()) of
                    Just k -> case h 2 == k 2 of
                                    True -> 1
                                    False -> 2 -- Unreachable
        Nothing -> 3

h :: (Int -> [Int -> Int]) -> Int
h g =
    case g 1 of
        [h] -> case g (one ()) of
                    [k] -> case h 2 == k 2 of
                                    True -> 1
                                    False -> 2 -- Unreachable
        [_, h] -> case g (one ()) of
                    [_, k] -> case h 2 == k 2 of
                                    True -> 3
                                    False -> 4 -- Unreachable
        (_:_:_:_) -> 5
        _ -> 6

{-# NOINLINE one #-}
one :: () -> Int
one _ = 1
