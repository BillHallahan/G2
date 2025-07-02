module Int1 where

-- True properties
p1 :: Int -> Bool
p1 n = (n - n == 0)

p2 :: Int -> Int -> Bool
p2 n m = m < 0 || (n - (n + m) <= 0)

p2' :: Int -> Int -> Bool
p2' n m = (n - (n + m) == -m)

p3 :: Int -> Bool
p3 n = (n - n == h n)

h :: Int -> Int
h n = if n == n + 1 then 1 else 0

p4 :: Int -> Bool
p4 n = n + 1 < n + 2

-- False properties
p1False :: Int -> Bool
p1False n = (n - n == if n == 2 then 1 else 0)

p2False :: Int -> Bool
p2False n = (n - n == if n == (100 * 100) then 1 else 0)

p2False' :: Int -> Int -> Bool
p2False' n m = (n - (n + m) == 0)

p3False :: Int -> Bool
p3False n = n < n
