{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, TypeApplications, ViewPatterns #-}

module Test2 where

import GHC.Prim2
import Control.Exception

callReplaceAll :: String -> String -> String -> (Int, String)
callReplaceAll x y z =
    let
        !r = strReplaceAll# x y z
    in
    case assert False (length r > length z) of
        True -> (1, r)
        False -> (2, r)