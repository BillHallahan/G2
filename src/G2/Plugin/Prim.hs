{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables #-}

module G2.Plugin.Prim where

import GHC.Exts

------------------------------------------------------------------------------
-- String Functions
------------------------------------------------------------------------------

-- pSMTEmpty
-- Just use []

-- pSMTUnit
-- Just use [x]

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

{-# NOINLINE pIsSMTRep# #-}
pIsSMTRep# :: [a] -> Bool
pIsSMTRep# _ = error "pIsSMTRep#"

data LitTableInfo a b = LTI { lit_table :: !(a -> b)
                            , lt_success :: !Bool
                            , lt_partial :: !(a -> Bool)
                            , lt_is_partial :: !Bool }

{-# NOINLINE pBuildLitTable# #-}
pBuildLitTable# :: (a -> b) -> LitTableInfo a b
pBuildLitTable# _ = error "pBuildLitTable#"

------------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------------

($&&) :: Bool -> Bool -> Bool
True $&& True = True
_ $&& _ = False