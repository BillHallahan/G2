{-# LANGUAGE BangPatterns #-}

module Regex where

import G2.Plugin
import Data.Char (ord)

{-# ANN isNum (SMTEquivIs "smtIsNum") #-}
isNum :: String -> Bool
isNum (num:rest) = ord num >= ord '0' && ord num <= ord '9' && isNum rest
isNum _ = True

smtIsNum :: String -> Bool
smtIsNum s =
    let !digit = smtReRange "0" "9"
        !many_digits = smtReStar digit
    in smtInRe s many_digits