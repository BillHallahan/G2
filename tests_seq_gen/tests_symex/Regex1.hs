{-# LANGUAGE BangPatterns, MagicHash, ScopedTypeVariables, TypeApplications, ViewPatterns #-}
module Spec where

import GHC.Prim2
import Control.Exception

regex1 :: String -> Int
regex1 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "abcdefghij"
        !re_union = re1 `reUnion#` re2 in
    case assert False (inRe# x re_union) of
        True | length x > 5 -> 1
             | otherwise -> 2
        False -> 3

regex2 :: String -> Int
regex2 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "xyz"
        !re_union = re1 `reUnion#` re2
        !re_inter = re1 `reInter#` re_union in
    case assert False (inRe# x re_inter) of
        True | x == "xyz" -> 1 -- Unreachable
             | otherwise -> 2
        False -> 3

regex3 :: String -> Int
regex3 x =
    let !re1 = toRe# "abc"
        !re_star = reStar# re1 in
    case assert False (inRe# x re_star) of
        True | length x > 31 -> 1
             | length x > 40 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex4 :: String -> Int
regex4 x =
    let !re1 = toRe# "abc"
        !re2 = toRe# "xyz"
        !re_concat = reConcat# re2 re1 in
    case assert False (inRe# x re_concat) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex5 :: String -> Int
regex5 x =
    let !re_all = reAll# @Char
        !re_none = reNone# @Char
        !re_union = re_all `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1
             | length x > 10 -> 2
             | otherwise -> 3
        False -> 4 -- Unreachable

regex6 :: String -> Int
regex6 x =
    let !re_all = reAllChar# @Char
        !re_none = reNone# @Char
        !re_union = re_all `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4

regex7 :: String -> Int
regex7 x =
    let !re_all = reAllChar# @Char
        !re_none = reNone# @Char
        !re_union = re_all `reUnion#` re_none
        !re_comp = reComp# re_union
    in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1 
             | length x > 1 -> 2
             | otherwise -> 3 -- Unreachable
        False -> 4

regex8 :: String -> Int
regex8 x =
    let !re_range = reRange# "a" "z"
        !re_none = reNone# @Char
        !re_union = re_range `reUnion#` re_none in
    case assert False (inRe# x re_union) of
        True | length x > 50 -> 1 -- Unreachable
             | length x > 10 -> 2 -- Unreachable
             | otherwise -> 3
        False -> 4
