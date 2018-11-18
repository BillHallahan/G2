module Pee where

data Peano = Succ Peano | Zero

{-@ add :: x:Peano -> y:Peano -> {z:Peano | toInt x < toInt z && toInt y < toInt z} @-}
add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add' p (Succ p2)

{-@ measure toInt @-}
toInt :: Peano -> Int
toInt Zero = 0
toInt (Succ p) = 1 + toInt p

add' :: Peano -> Peano -> Peano
add' Zero p = p
add' (Succ p) p2 = add' p (Succ p2)

{-@ isZero :: p:Peano -> {b:Bool | toInt p == 0} @-}
isZero :: Peano -> Bool
isZero Zero = True
isZero (Succ _) = False

{-@ fromInt :: v:Int -> {p:Peano | v > 0} @-}
fromInt :: Int -> Peano
fromInt 0 = Zero
fromInt n = Succ (fromInt' (n - 1))

fromInt' :: Int -> Peano
fromInt' 0 = Zero
fromInt' n = Succ (fromInt' (n - 1))
