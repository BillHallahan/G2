module Test where

import Data.List

f1 :: String -> String -> String -> String
f1 xs ys zs = xs ++ ys ++ zs

f2 :: String -> String -> Int
f2 xs ys = length xs + length ys

f3 :: String -> String -> Bool
f3 xs ys = take (length xs) ys == xs 

f4 :: String -> String -> Bool
f4 [] [] = True
f4 _ [] = False
f4 xs ys@(_:ys') | take (length xs) ys == xs = True
                 | otherwise = f4 xs ys'

f5 :: String -> String -> String -> (String, String)
f5 xs ys zs = (xs ++ ys, ys ++ zs)

f6 :: String -> Maybe String
f6 [] = Nothing
f6 (x:xs) = Just xs

f7 :: String -> String -> Maybe (Either String String)
f7  x y | x < y = Just $ Left x
        | y < x = Just $ Right y
        | otherwise = Nothing

f8 :: String -> String -> Either String String
f8  x y | x < y = Left x
        | y < x = Right y
        | otherwise = error "f8"

f9 :: [a] -> [a] -> [a] -> [a]
f9 xs ys zs = xs ++ ys ++ zs

f10 :: Char -> [Char] -> [Char]
f10 x xs = x:xs

f11 :: Char -> [Char] -> [Char]
f11 x xs = xs ++ [x]

f12 :: [Char] -> Maybe Char
f12 [] = Nothing
f12 (x:_) = Just x

f13 :: [Char] -> Maybe Char
f13 [] = Nothing
f13 [x] = Just x
f13 (_:xs) = f13 xs

f14 :: Int -> String -> Int
f14 x [] = x
f14 _ xs = length xs

f15 :: Integer -> String -> Integer
f15 x [] = x
f15 _ xs = genericLength xs

f16 :: Eq a => a -> [a] -> [a]
f16  _ [] = []
f16 x (y:ys) = if x == y then ys else y : f16 x ys

f17 :: Num a => Integer -> a
f17 x = fromInteger x + fromInteger x

f18 :: Integral a => a -> Integer
f18 x = toInteger x + toInteger x
