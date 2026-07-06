module Challenge where

import Control.Exception

data AB = A AB | B deriving Eq

{-# NOINLINE abInf #-}
abInf :: () -> AB
abInf = abInf

{-# NOINLINE b #-}
b :: () -> AB
b () = A B

data XYZ = X | Y | Z

abc1 :: (Int -> AB -> XYZ) -> Int
abc1 f = case f 1 B of
                X -> case f 1 (A B) of
                            Y -> case f 2 (abInf ()) of
                                    Z -> 1
                                    _ -> 2
                            _ -> 3
                _ -> 4

abc2 :: (Int -> AB -> AB -> XYZ) -> Int
abc2 f =
    case f 1 (A B) B of
        X -> case f 1 (A (b ())) (abInf ()) of
                Y -> 1
                _ -> 2
        _ -> 3

abc3 :: (Int -> AB -> Bool) -> Int
abc3 f =
    case f 1 (abInf ()) of
        True -> case f 2 (A B) of
                    True -> case f 2 B of
                                False -> 1
                                _ -> 2
                    _ -> 3
        _ -> 4

abc4 :: (AB -> Int -> Bool) -> Int
abc4 f =
    case f (abInf ()) 1 of
        True -> case f (A B) 2 of
                    True -> case f B 2 of
                                False -> 1
                                _ -> 2
                    _ -> 3
        _ -> 4

data Funcs = I (Int -> Int) | I2 (Int -> Int -> Int) | B2 (Int -> Bool)

funcs :: (Funcs -> Int) -> Int
funcs f =
    case f (I (\x -> x)) == f (I (\x -> x + 1)) of
        True -> 1
        False -> case f (B2 (> 0)) == f (B2 (< 10)) of
                    True -> 2
                    False -> 3

maybeFuncs :: (Maybe Funcs -> Int) -> Int
maybeFuncs f =
    case f (Just (I id)) == f Nothing of
        True -> 1
        False -> case f (Just (I id)) == f (Just (B2 $ const True)) of
                    True -> case f (Just (I id)) == f (Just (I (\x -> x * 2))) of
                                True -> 2
                                False -> 3
                    False -> 4
