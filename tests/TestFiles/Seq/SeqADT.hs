module SeqADT where

data Nat = S Nat | Z deriving Eq

data Pair a b = Pair a b deriving Eq

-- CONFIG: --smt-lists --smt-adts Nat,Pair

conLen :: [Pair Nat Int] -> [Pair Nat Int] -> [Pair Nat Int]
conLen xs ys | length xs > length ys = xs ++ ys
             | length xs > 3, length ys > length xs = ys ++ xs ++ ys
             | length xs > 3, length ys <= length xs = ys ++ [Pair Z 2] ++ xs
             | length ys > length xs = ys ++ xs
             | otherwise = []

pairExtract :: [Pair Nat Int] -> Nat
pairExtract [Pair Z _] = S Z
pairExtract [Pair x _] = S (S x)
pairExtract xs | length xs > 10 = S (S (S Z))
pairExtract (Pair Z _:_) = S (S (S (S Z)))
pairExtract (Pair x _:_) = x
pairExtract [] = S (S Z) 