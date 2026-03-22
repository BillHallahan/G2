module IdCall where

import Prelude hiding (map)

idCall :: [Int] -> Bool
idCall xs = [y | x <- xs, y <- [x]] == [y | x <- xs, y <- [x]]

ds5'2 x = (\ds6'2 -> case ds6'2 of
                        []  -> ds'2 x
                        ds8'2 : ds9'2 -> (:) ds8'2 (ds5'2 x ds9'2))
                        
ds'2 = (\ds1'2 -> case ds1'2 of
            []  -> []
            ds3'2 : ds4'2 -> ds5'2 ds4'2 ( ds3'2 :([])))

ds5 x = (\ds6 -> case ds6 of
                        []  -> ds x
                        ds8 : ds9 -> (:) ds8 (ds5 x ds9))
ds = (\ds1 -> case ds1 of
            []  -> []
            ds3 : ds4 -> let
                   in ds5 ds4 (ds3 :([])))

idCall2 :: ([] Int) -> Bool
idCall2 = (\xs -> (==) ( ds'2 xs) ( ds xs))

data A = A deriving Eq

p1 :: [A -> A] -> [A -> A] -> [A] -> Bool
p1 u v w = ( (repeat (.)) <**> u <**> v <**> w) == (u <**> (v <**> w))

(<**>) :: [a -> b] -> [a] -> [b]
fs <**> xs = zipWith id fs xs

infixl 4 <**>
