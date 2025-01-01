module Double where

double :: Int -> Int
double x = x + x

{-@ main :: x:Int -> { r:Int | r == 2 * x } @-} 
main :: Int -> Int
main x = double x