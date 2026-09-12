module NonTerm where

import G2.Plugin

{-# ANN nonTerm1 (SMTEquivIs "smtNonTerm1") #-}
nonTerm1 :: [Int] -> [Int]
nonTerm1 = nonTerm1

smtNonTerm1 :: [Int] -> [Int]
smtNonTerm1 xs = xs

{-# ANN nonTerm2 (SMTEquivIs "smtNonTerm2") #-}
nonTerm2 :: [Int] -> [Int]
nonTerm2 = nonTerm2

smtNonTerm2 :: [Int] -> [Int]
smtNonTerm2 xs = xs

{-# ANN nonTerm3 (SMTEquivIs "smtNonTerm3") #-}
nonTerm3 :: [Int] -> [Int] -> [Int]
nonTerm3 [] ys = nonTerm3 [] ys
nonTerm3 (x:xs) ys = x:nonTerm3 xs ys

smtNonTerm3 :: [Int] -> [Int] -> [Int]
smtNonTerm3 xs ys = xs $++ ys

{-# ANN dontCheck (SMTEquivIsWithConfig "smtDontCheck" "--no-term-check")
    #-}
dontCheck :: [Int] -> [Int]
dontCheck = dontCheck

smtDontCheck :: [Int] -> [Int]
smtDontCheck xs = xs
