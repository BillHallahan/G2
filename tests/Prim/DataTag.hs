{-# LANGUAGE MagicHash #-}

module DataTag where

import GHC.Exts

data ABCD = A | B | C | D | E  deriving Eq

dataToTag1 :: (Int, Int)
dataToTag1 = (I# (dataToTag# C), I# (dataToTag# E))

dataToTag2 :: ABCD -> Int
dataToTag2 abcd = I# (dataToTag# abcd)

dataToTag3 :: ABCD -> Int
dataToTag3 A = -100
dataToTag3 B = -200
dataToTag3 C = -300
dataToTag3 E = -400
dataToTag3 d = I# (dataToTag# d)

tagToEnum1 :: (ABCD, ABCD)
tagToEnum1 = (tagToEnum# 2#, tagToEnum# 4#)

tagToEnum2 :: (ABCD, ABCD)
tagToEnum2 = (tagToEnum# 1#, tagToEnum# 24#)

tagToEnum3 :: Int -> Maybe ABCD
tagToEnum3 (I# x) = if isTrue# (x >=# 0#) && isTrue# (x <=# 4#)
                            then Just (tagToEnum# x)
                            else Nothing

tagToEnum4 :: Int -> Maybe ABCD
tagToEnum4 (I# x) = if isTrue# (x >=# 0#) && isTrue# (x <=# 3#)
                            then Just (tagToEnum# (1# +# x))
                            else Nothing