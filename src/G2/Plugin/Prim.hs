{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}

module G2.Plugin.Prim ( module G2.Plugin.Prim
                      , LitTableInfo (..)) where

import Data.List
import GHC.Exts
import GHC.Prim2

------------------------------------------------------------------------------
-- String Functions
------------------------------------------------------------------------------

-- pSMTEmpty
-- Just use []

-- pSMTUnit
-- Just use [x]

{-# NOINLINE pSmtEq# #-}
pSmtEq# :: Eq a => [a] -> [a] -> Bool
pSmtEq# = (==)

{-# NOINLINE pSmtLen# #-}
pSmtLen# :: [a] -> Int#
pSmtLen# xs = case length xs of I# x -> x

{-# NOINLINE pSmtNth# #-}
pSmtNth# :: [a] -> Int# -> a
pSmtNth# (x:_) 0# = x
pSmtNth# (_:xs) n | I# n > 0 = pSmtNth# xs (n -# 1#)
pSmtNth# _ _ = error "pSmtNth#: invalid index"

{-# NOINLINE pSmtUpdate# #-}
pSmtUpdate# :: [a] -> Int# -> [a] -> [a]
pSmtUpdate# _ = error "pSmtUpdate#"

{-# NOINLINE pSmtExtract# #-}
pSmtExtract# :: [a] -> Int# -> Int# -> [a]
pSmtExtract# xs start len = take (I# len) $ drop (I# start) xs

{-# NOINLINE pSmtAppend# #-}
pSmtAppend# :: [a] -> [a] -> [a]
pSmtAppend# = (++)

{-# NOINLINE pSmtAt# #-}
pSmtAt# :: [a] -> Int# -> [a]
pSmtAt# (x:_) 0# = [x]
pSmtAt# (_:xs) n | I# n > 0 = pSmtAt# xs (n -# 1#)
pSmtAt# _ _ = []

{-# NOINLINE pSmtContains# #-}
pSmtContains# :: Eq a => [a] -> [a] -> Bool
pSmtContains# = isInfixOf

{-# NOINLINE pSmtIndexOf# #-}
pSmtIndexOf# :: Eq a => [a] -> [a] -> Int# -> Int#
pSmtIndexOf# xs ys i = go i (drop (I# i) ys)
    where
        go j zs | isPrefixOf xs zs = j
        go j (_:zs) = go (j +# 1#) zs
        go _ [] = -1#

{-# NOINLINE pSmtReplace# #-}
pSmtReplace# :: [a] -> [a] -> [a] -> [a]
pSmtReplace# _ _ = error "pSmtReplace#"

{-# NOINLINE pSmtReplaceAll# #-}
pSmtReplaceAll# :: [a] -> [a] -> [a] -> [a]
pSmtReplaceAll# _ _ = error "pSmtReplaceAll#"

{-# NOINLINE pSmtReverse# #-}
pSmtReverse# :: [a] -> [a]
pSmtReverse# = reverse

{-# NOINLINE pSmtPrefixOf# #-}
pSmtPrefixOf# :: Eq a => [a] -> [a] -> Bool
pSmtPrefixOf# = isPrefixOf

{-# NOINLINE pSmtSuffixOf# #-}
pSmtSuffixOf# :: Eq a => [a] -> [a] -> Bool
pSmtSuffixOf# = isSuffixOf

{-# NOINLINE pSmtMap# #-}
pSmtMap# :: (a -> b) -> [a] -> [b]
pSmtMap# = map

{-# NOINLINE pSmtFoldLeft# #-}
pSmtFoldLeft# :: (a -> b -> a) -> a -> [b] -> a
pSmtFoldLeft# = foldl'

{-# NOINLINE pSmtFoldLeftI# #-}
pSmtFoldLeftI# :: (Int# -> a -> b -> a) -> Int# -> a -> [b] -> a
pSmtFoldLeftI# = error "pSmtFoldLeftI#"

{-# NOINLINE pSmtReRange# #-}
pSmtReRange# :: [a] -> [a] -> [a]
pSmtReRange# = error "pSmtReRange#"

{-# NOINLINE pSmtInRe# #-}
pSmtInRe# :: [a] -> [a] -> Bool
pSmtInRe# = error "pSmtInRe#"

{-# NOINLINE pSmtToRe# #-}
pSmtToRe# :: [a] -> [a]
pSmtToRe# = error "pSmtToRe#"

{-# NOINLINE pSmtReNone# #-}
pSmtReNone# :: [a]
pSmtReNone# = error "pSmtReNone#"

{-# NOINLINE pSmtReAll# #-}
pSmtReAll# :: [a]
pSmtReAll# = error "pSmtReAll#"

{-# NOINLINE pSmtReAllChar# #-}
pSmtReAllChar# :: [a]
pSmtReAllChar# = error "pSmtReAllChar#"

{-# NOINLINE pSmtReConcat# #-}
pSmtReConcat# :: [a] -> [a] -> [a]
pSmtReConcat# = error "pSmtReConcat#"

{-# NOINLINE pSmtReUnion# #-}
pSmtReUnion# :: [a] -> [a] -> [a]
pSmtReUnion# = error "pSmtReUnion#"

{-# NOINLINE pSmtReInter# #-}
pSmtReInter# :: [a] -> [a] -> [a]
pSmtReInter# = error "pSmtReInter#"

{-# NOINLINE pSmtReStar# #-}
pSmtReStar# :: [a] -> [a]
pSmtReStar# = error "pSmtReStar#"

{-# NOINLINE pSmtReComp# #-}
pSmtReComp# :: [a] -> [a]
pSmtReComp# = error "pSmtReComp#"

{-# NOINLINE pIsSMTRep# #-}
pIsSMTRep# :: [a] -> Bool
pIsSMTRep# _ = error "pIsSMTRep#"

{-# NOINLINE pBuildLitTable# #-}
pBuildLitTable# :: (a -> b) -> LitTableInfo a b
pBuildLitTable# _ = error "pBuildLitTable#"

{-# NOINLINE pSymGen# #-}
pSymGen# :: a
pSymGen# = error "pSymGen#"

------------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------------

{-# NOINLINE ($&&) #-}
($&&) :: Bool -> Bool -> Bool
True $&& True = True
_ $&& _ = False

{-# NOINLINE ($||) #-}
($||) :: Bool -> Bool -> Bool
True $|| _ = True
_ $|| b = b
