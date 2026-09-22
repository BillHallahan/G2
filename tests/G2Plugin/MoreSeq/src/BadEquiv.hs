module BadEquiv where

import G2.Plugin

{-# ANN module ("--smt-tuples --smt-adts MyI,A")
    #-}

{-# ANN badEquiv (SMTEquivIs "smtBadEquiv")#-}
badEquiv :: [Int] -> Int
badEquiv [] = 1
badEquiv _ = 2

smtBadEquiv :: [Int] -> Int
smtBadEquiv _ = 1

{-# ANN badEquivProp Prop #-}
badEquivProp :: [Int] -> Bool
badEquivProp xs = badEquiv xs == 1

{-# ANN headFalse (SMTEquivIs "headFalseSMT")
    #-}
headFalse :: [Int] -> Int
headFalse [] = 0
headFalse (x:_) = x

headFalseSMT :: [Int] -> Int
headFalseSMT xs = smtNth xs $ -1
