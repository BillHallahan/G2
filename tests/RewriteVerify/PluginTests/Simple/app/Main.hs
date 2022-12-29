module Main where


f :: Int -> Int
f x = x

g :: Int -> Int
g x = x

one :: Int -> Int
one x = 1


{-# RULES
"fg" forall x . f x = g x
"f_one" forall x . f x = one x
  #-}

main :: IO ()
main = putStrLn "Hello, Haskell!"
