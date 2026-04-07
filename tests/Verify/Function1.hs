module Function1 where

p1 :: Int -> (Int -> Int) -> Bool
p1 e f = (fmap id f) e == f e

p1False :: Int -> Int -> (Int -> Int) -> Bool
p1False e1 e2 f = (fmap id f) e1 == f e2