module Error1 where

f :: Int -> Int
f x = x + (error "Error")

g :: Int -> Int
g x = h x (error "Error")

h :: Int -> Int -> Int
h x y = x * y
