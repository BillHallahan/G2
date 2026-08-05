{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}

module G2.Plugin.Prim ( module G2.Plugin.Prim
                      , LitTableInfo (..)) where

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
pSmtEq# :: [a] -> [a] -> Bool
pSmtEq# _ _ = True

{-# NOINLINE pSmtLen# #-}
pSmtLen# :: [a] -> Int#
pSmtLen# _ = 0#

{-# NOINLINE pSmtNth# #-}
pSmtNth# :: [a] -> Int# -> a
pSmtNth# _ = error "pSmtNth#"

{-# NOINLINE pSmtUpdate# #-}
pSmtUpdate# :: [a] -> Int# -> [a] ->[a]
pSmtUpdate# _ = error "pSmtUpdate#"

{-# NOINLINE pSmtExtract# #-}
pSmtExtract# :: [a] -> Int# -> Int# ->[a]
pSmtExtract# _ = error "pSmtExtract#"

{-# NOINLINE pSmtAppend# #-}
pSmtAppend# :: [a] -> [a] -> [a]
pSmtAppend# _ _ = error "pSmtAppend#"

{-# NOINLINE pSmtAt# #-}
pSmtAt# :: [a] -> Int# -> [a]
pSmtAt# _ _ = error "pSmtAt#"

{-# NOINLINE pSmtContains# #-}
pSmtContains# :: [a] -> [a] -> Bool
pSmtContains# _ _ = error "pSmtContains#"

{-# NOINLINE pSmtIndexOf# #-}
pSmtIndexOf# :: [a] -> [a] -> Int# -> Int#
pSmtIndexOf# _ _ = error "pSmtIndexOf#"

{-# NOINLINE pSmtReplace# #-}
pSmtReplace# :: [a] -> [a] -> [a] -> [a]
pSmtReplace# _ _ = error "pSmtReplace#"

{-# NOINLINE pSmtReplaceAll# #-}
pSmtReplaceAll# :: [a] -> [a] -> [a] -> [a]
pSmtReplaceAll# _ _ = error "pSmtReplaceAll#"

{-# NOINLINE pSmtReverse# #-}
pSmtReverse# :: [a] -> [a]
pSmtReverse# _ = error "pSmtReverse#"

{-# NOINLINE pSmtPrefixOf# #-}
pSmtPrefixOf# :: [a] -> [a] -> Bool
pSmtPrefixOf# _ _ = error "pSmtPrefixOf#"

{-# NOINLINE pSmtSuffixOf# #-}
pSmtSuffixOf# :: [a] -> [a] -> Bool
pSmtSuffixOf# _ _ = error "pSmtSuffixOf#"

{-# NOINLINE pSmtMap# #-}
pSmtMap# :: (a -> b) -> [a] -> [b]
pSmtMap# = error "pSmtMap#"

{-# NOINLINE pSmtFoldLeft# #-}
pSmtFoldLeft# :: (a -> b -> a) -> a -> [b] -> a
pSmtFoldLeft# = error "pSmtFoldLeft#"

{-# NOINLINE pSmtFoldLeftI# #-}
pSmtFoldLeftI# :: (Int# -> a -> b -> a) -> Int# -> a -> [b] -> a
pSmtFoldLeftI# = error "pSmtFoldLeftI#"

{-# NOINLINE pSmtReRange# #-}
pSmtReRange# :: String -> String -> String
pSmtReRange# = error "pSmtReRange#"

{-# NOINLINE pSmtInRe# #-}
pSmtInRe# :: String -> String -> Bool
pSmtInRe# = error "pSmtInRe#"

{-# NOINLINE pSmtToRe# #-}
pSmtToRe# :: String -> String
pSmtToRe# = error "pSmtToRe#"

{-# NOINLINE pSmtReNone# #-}
pSmtReNone# :: String
pSmtReNone# = error "pSmtReNone#"

{-# NOINLINE pSmtReAll# #-}
pSmtReAll# :: String
pSmtReAll# = error "pSmtReAll#"

{-# NOINLINE pSmtReAllChar# #-}
pSmtReAllChar# :: String
pSmtReAllChar# = error "pSmtReAllChar#"

{-# NOINLINE pSmtReConcat# #-}
pSmtReConcat# :: String -> String -> String
pSmtReConcat# = error "pSmtReConcat#"

{-# NOINLINE pSmtReUnion# #-}
pSmtReUnion# :: String -> String -> String
pSmtReUnion# = error "pSmtReUnion#"

{-# NOINLINE pSmtReInter# #-}
pSmtReInter# :: String -> String -> String
pSmtReInter# = error "pSmtReInter#"

{-# NOINLINE pSmtReStar# #-}
pSmtReStar# :: String -> String
pSmtReStar# = error "pSmtReStar#"

{-# NOINLINE pSmtReComp# #-}
pSmtReComp# :: String -> String
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

($&&) :: Bool -> Bool -> Bool
True $&& True = True
_ $&& _ = False
