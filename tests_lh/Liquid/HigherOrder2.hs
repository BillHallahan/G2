module HigherOrder2 where

data X = X | Y

{-@ measure isY :: X -> Bool
        isY X = False
        isY Y = True
@-}

{-@ f :: (X -> Int) -> Int@-}
f :: (X -> Int) -> Int
f g = g X

{-@ yToInt :: x:{v:X | isY v} -> Int @-}
yToInt :: X -> Int
yToInt Y = 0
yToInt X = die "X"

{-@ h :: (X -> Int) -> Int @-}
h :: (X -> Int) -> Int
h g = g (die "Bad!")

{-@ die :: s:{ String | false } -> a @-}
die :: String -> a
die = error
