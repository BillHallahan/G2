{-# LANGUAGE MagicHash #-}
module MoreSeq where

import G2.Plugin hiding ((==>))

{-# ANN module ("--smt-tuples --smt-adts MyI,A")
    #-}

{-
{-# ANN f (SMTEquivIsWithConfig "fSMT" "")
    #-}
f :: [(Int, Int)] -> [(Int, Int)]
f [] = []
f ((x, y):xs) | x > 0 = (x, y):f xs
              | otherwise = (x, y + 1):f xs

fSMT :: [(Int, Int)] -> [(Int, Int)]
fSMT = smtMap (\(x, y) -> if x > 0 then (x, y) else (x, y + 1))
-}

{-# ANN g (SMTEquivIsWithConfig "gSMT" "")
    #-}
g :: [(Int, Int)] -> [Int]
g [] = []
g ((x, y):xs) | x > 0 = x:g xs
              | otherwise = y:g xs

gSMT :: [(Int, Int)] -> [Int]
gSMT = smtMap (\(x, y) -> if x > 0 then x else y)

data A = A | B

instance Eq A where
    A == A = True
    B == B = True
    _ == _ = False

data MyI = MyI A deriving Eq

{-# ANN h (SMTEquivIsWithConfig "hSMT" "--smt-timeout 30")
    #-}
h :: [(MyI, MyI)] -> [MyI]
h [] = []
h ((MyI x, y):xs) | x == A = MyI x:h xs
                  | otherwise = y:h xs

hSMT :: [(MyI, MyI)] -> [MyI]
hSMT = smtMap (\(MyI x, y) -> if x == A then MyI x else y)

rotate :: Int -> [a] -> [a]
rotate 0     xs     = xs
rotate _     []     = []
rotate n     (x:xs) = rotate (n - 1) (xs ++ [x])

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

(==>) :: Bool -> Bool -> Bool
(==>) = given
infixr 0 ==>

{-# ANN prop_rot Prop  #-}
prop_rot   n m ys xs = rotate n (xs :: [Int]) == rotate m ys ==> n == m
