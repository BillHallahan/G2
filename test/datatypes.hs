module DataTypes where

data X = A Y | B | C | D (Int -> Int) | E (Int -> Int) (Int -> Int) | F Int

data Y = G | H Int | I

f :: X -> X
f (A G) = C
f (A y) = B
f B = A (H 8)
f C = C
f (D h) = F (h 8)
f x = x

g :: Y -> X
g G = B
g _ = C

intToInt :: Int -> Int
intToInt x = x + 3

xApp :: X
xApp = D intToInt

xApp2 :: X
xApp2 = E intToInt intToInt