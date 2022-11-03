{-# LANGUAGE MagicHash #-}

module DataTag where

import GHC.Exts

data ABCD = A | B | C | D | E | F | G | H | I | J | K deriving Eq

dataToTag1 :: (Int, Int)
dataToTag1 = (I# (dataToTag# C), I# (dataToTag# G))

dataToTag2 :: ABCD -> Int
dataToTag2 abcd = I# (dataToTag# abcd)

tagToEnum1 :: (ABCD, ABCD)
tagToEnum1 = (tagToEnum# 5#, tagToEnum# 8#)

tagToEnum2 :: (ABCD, ABCD)
tagToEnum2 = (tagToEnum# 5#, tagToEnum# 24#)

tagToEnum3 :: Int -> ABCD
tagToEnum3 (I# x)= tagToEnum# x