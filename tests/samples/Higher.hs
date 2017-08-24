module Higher where

square :: Int -> Int
square x = x * x

plus5 :: Int -> Int
plus5 x = x + 5

const :: Int -> Int
const x = x

foo :: Int -> Int -> Int -> Int
foo a b c = if a + b < c
                then a + b
                else if c < 5
                    then b + c
                    else a + c

-- Higher order functions below

fixed :: (Int -> Int) -> Int -> Bool
fixed f x = f x == f (f x)

