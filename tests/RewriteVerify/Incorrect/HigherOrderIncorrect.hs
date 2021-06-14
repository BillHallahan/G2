module HigherOrderIncorrect where

int :: Int -> Int
int x = x

{-# RULES
"direct" forall (f :: Int -> Int) (g :: Int -> Int) . int (f (g 1)) = int (f 1)
  #-}