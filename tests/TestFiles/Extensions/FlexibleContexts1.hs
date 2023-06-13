{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module FlexibleContexts1 where

class F a where
    f :: a -> a

instance F [Char] where
    f [] = []
    f (x:xs) = x:x:xs

instance F [Float] where
    f [] = []
    f (x:xs) = x + 1:xs
    
callF :: F a => a -> a
callF = f

callF2 :: F [a] => [a] -> [a]
callF2 xs = f xs

callF3 :: F [a] => [a] -> [a]
callF3 = f