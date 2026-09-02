module Exists where

import G2.Plugin

{-# ANN exists1 (SMTEquivIsWithConfig "smtExists1" "")
    #-}
exists1 :: [Int] -> [Int]
exists1 xs = xs

smtExists1 :: [Int] -> [Int]
smtExists1 _ = exists (\_ -> False)

data AB = A | B deriving Eq

{-# ANN exists2 (SMTEquivIsWithConfig "smtExists2" "")
    #-}
exists2 :: AB -> [Int] -> [Int]
exists2 A xs = xs
exists2 B xs = xs ++ xs

smtExists2 :: AB -> [Int] -> [Int]
smtExists2 ab xs = exists (\ys -> case ab of
                                    A -> xs == ys
                                    B -> False)

{-# ANN exists3 (SMTEquivIsWithConfig "smtExists3" "--smt-adts AB")
    #-}
exists3 :: AB -> [Int] -> [Int]
exists3 A xs = xs
exists3 B xs = xs ++ xs

smtExists3 :: AB -> [Int] -> [Int]
smtExists3 ab xs = exists (\ys -> case ab of
                                    A -> xs == ys
                                    B -> False)


{-# ANN exists4 (SMTEquivIsWithConfig "smtExists4" "")
    #-}
exists4 :: [Int] -> [Int]
exists4 xs = xs

smtExists4 :: [Int] -> [Int]
smtExists4 _ = exists (\_ -> (1 :: Int) < 0)

{-# ANN exists5 (SMTEquivIsWithConfig "smtExists5" "")
    #-}
exists5 :: [Int] -> [Int]
exists5 xs = xs

smtExists5 :: [Int] -> [Int]
smtExists5 _ = exists (\_ -> "hello" == "hi")

{-# ANN exists6 (SMTEquivIsWithConfig "smtExists6" "")
    #-}
exists6 :: AB -> [Int] -> [Int]
exists6 ab xs = 1:(case ab of A -> xs; B -> xs ++ xs)

smtExists6 :: AB -> [Int] -> [Int]
smtExists6 ab xs = exists (\ys -> case ab of
                                    A -> 1:xs == ys
                                    B -> False)

{-# ANN exists7 (SMTEquivIsWithConfig "smtExists7" "")
    #-}
exists7 :: AB -> [Int] -> [Int]
exists7 _ xs = xs

smtExists7 :: AB -> [Int] -> [Int]
smtExists7 ab xs = exists (\ys -> case ab of
                                    A -> xs == ys
                                    B -> False)

{-# ANN exists8 (SMTEquivIsWithConfig "smtExists8" "")
    #-}
exists8 :: Int -> [Int] -> [Int]
exists8 _ xs = xs

smtExists8 :: Int -> [Int] -> [Int]
smtExists8 x xs = exists (\ys -> case x > 0 of
                                    True -> xs == ys
                                    False -> False)
