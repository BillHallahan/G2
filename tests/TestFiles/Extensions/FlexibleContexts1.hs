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

class G a where
    g :: a -> a

instance G (Int, Float) where
    g (x, y) = (x + 1, y)

instance G (Char, Int) where
    g (x, y) = (x, y + 1)

callG :: G a => a -> a
callG = g

callG2 :: G (a, b) => (a, b) -> (a, b)
callG2 = g