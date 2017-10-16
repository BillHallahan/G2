module BadNames1 where

data X' = X' X' | Y' | Z'

abs' :: Int -> Int
abs' x
    | x >= 0 = x
    | otherwise = -x

xswitch :: X' -> X'
xswitch (X' x) = X' (xswitch x)
xswitch Y' = Z'
xswitch Z' = Y'