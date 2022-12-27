module BadRep where

{-@ measure size      :: [a] -> Int
    size []        = 0
    size (x:xs) = 1 + size xs
  @-}

{-@ replicate :: n:Nat -> a -> {l: [a] | n = (size l)} @-}
replicate :: Int -> a -> [a]
replicate 0 _ = []
replicate n x = replicate (n - 1) x
