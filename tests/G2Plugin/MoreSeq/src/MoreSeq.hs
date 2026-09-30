{-# LANGUAGE MagicHash #-}
module MoreSeq where

import G2.Plugin hiding ((==>))

{-# ANN module ("--smt-lists --smt-strings --smt-tuples --smt-adts MyI,A")
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

{-# ANN (+++) (SMTEquivIs "appendSMT") #-}
(+++) :: [a] -> [a] -> [a]
[]     +++ ys = ys
(x:xs) +++ ys = x : (xs +++ ys)

appendSMT :: [a] -> [a] -> [a]
appendSMT = ($++)

rotate :: Int -> [a] -> [a]
rotate 0     xs     = xs
rotate _     []     = []
rotate n     (x:xs) = rotate (n - 1) (xs +++ [x])

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

(==>) :: Bool -> Bool -> Bool
(==>) = given
infixr 0 ==>

{-# ANN prop_rot Prop #-}
prop_rot :: Int -> Int -> [Int] -> [Int] -> Bool
prop_rot   n m ys xs = rotate n (xs :: [Int]) == rotate m ys ==> n == m

(=/=) :: Eq a => a -> a -> Bool
x =/= y = not (x == y)

{-# ANN len (SMTEquivIs "lenSMT") #-}
len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + (len xs)

lenSMT :: [a] -> Int
lenSMT = smtLen

{-# ANN prop_rot2 (PropWithConfig "--smt cvc5")
    #-}
prop_rot2 :: Int -> Int -> [Int] -> [Int] -> Bool
prop_rot2  n m ys xs = (n < len xs) == True ==> (m < len ys) == True ==> xs == ys ==> rotate 1 xs =/= xs ==> rotate n (xs :: [Int]) == rotate m ys ==> n == m

{-# ANN update (SMTEquivIsWithConfig "updateSMT" "--smt cvc5")
    #-}
update :: [Int] -> Int -> [Int] -> [Int]
update xs i _ | i < 0 = xs
update (_:xs) 0 (y:ys) = y:update xs 0 ys
update xs 0 [] = xs
update (x:xs) i ys = x:update xs (i - 1) ys
update [] _ _ = []

updateSMT :: [Int] -> Int -> [Int] -> [Int]
updateSMT = smtUpdate

{-# ANN prop_update_bad (PropWithConfig "--smt z3")
    #-}
prop_update_bad :: [Int] -> [Int] -> Int -> [Int] -> Bool
prop_update_bad xs ys n rep = (update xs n rep) == (update ys n rep) ==> xs == ys

{-# ANN prop_update (PropWithConfig "--smt z3")
    #-}
prop_update :: [Int] -> [Int] -> Int -> [Int] -> Bool
prop_update xs ys n rep = xs == ys ==> (update xs n rep) == (update ys n rep)

-- Simpler props to test that z3 doesn't error on a lack of seq.update,
-- since it times out on the above properties :(
{-# ANN prop_update_simple (PropWithConfig "--smt z3")
    #-}
prop_update_simple :: [Int] -> Bool
prop_update_simple xs = update xs 0 [] == xs

{-# ANN prop_update_neg_index (PropWithConfig "--smt z3")
    #-}
prop_update_neg_index :: [Int] -> [Int] -> Bool
prop_update_neg_index xs rep = update xs (-1) rep == xs

{-# ANN prop_update_empty_rep (PropWithConfig "--smt z3")
    #-}
prop_update_empty_rep :: [Int] -> Int -> Bool
prop_update_empty_rep xs n = update xs n [] == xs

{-# ANN prop_update_empty_list (PropWithConfig "--smt z3")
    #-}
prop_update_empty_list :: Int -> [Int] -> Bool
prop_update_empty_list n rep = update [] n rep == []

{-# ANN prop_update_single (PropWithConfig "--smt z3")
    #-}
prop_update_single :: Int -> Int -> Bool
prop_update_single x y = update [x] 0 [y] == [y]

{-# ANN prop_update_len (PropWithConfig "--smt z3")
    #-}
prop_update_len :: [Int] -> Int -> [Int] -> Bool
prop_update_len xs n rep = len (update xs n rep) == len xs

{-# ANN count (SMTEquivIsWithConfig "countSMT" "--no-string-simplifier --smt cvc5,z3 --smt-timeout 2")
    #-}
count :: Int -> [Int] -> Int
count _ [] = 0
count x (y:ys) =
  case x == y of
    True -> 1 + (count x ys)
    _ -> count x ys

countSMT :: Int -> [Int] -> Int
countSMT e xs = (smtLen xs) - (smtLen (smtReplaceAll xs [e] []))


{-# ANN myLast (SMTEquivIsWithConfig "lastSMT" "--smt cvc5,z3 --no-string-simplifier")
    #-}
myLast :: [Int] -> Int
myLast [] = 0
myLast [x] = x
myLast (_:xs) = myLast xs

lastSMT :: [Int] -> Int
lastSMT xs =
  if smtLen xs == 0
    then 0
    else smtNth xs $ smtLen xs - 1
