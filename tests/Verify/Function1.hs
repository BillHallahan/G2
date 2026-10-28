module Function1 where

p1 :: Int -> (Int -> Int) -> Bool
p1 e f = (fmap id f) e == f e

p1False :: Int -> Int -> (Int -> Int) -> Bool
p1False e1 e2 f = (fmap id f) e1 == f e2

p2 :: Int -> (Int -> (Int -> Int)) -> (Int -> (Int -> Int)) -> (Int -> Int) -> Bool
p2 e u v w = (pure (.) <*> u <*> v <*> w) e == (u <*> (v <*> w)) e
