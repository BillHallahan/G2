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
